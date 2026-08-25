/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate556 : CompactCertificate where
  left := 427
  right := 428
  center := 855 / 2
  grid := fun i =>
    match i.val with
    | 0 => 136
    | 1 => 100
    | 2 => 162
    | 3 => 29
    | 4 => 79
    | 5 => 213
    | 6 => 157
    | 7 => 269
    | 8 => 198
    | 9 => 304
    | 10 => 176
    | 11 => 312
    | 12 => 291
    | 13 => 208
    | 14 => 236
    | 15 => 197
    | 16 => 174
    | 17 => 252
    | 18 => 139
    | 19 => 118
    | 20 => 74
    | 21 => 40
    | 22 => 108
    | 23 => 147
    | 24 => 62
    | 25 => 253
    | _ => 169
  point := fun i =>
    match i.val with
    | 0 => 855 / 2
    | 1 => 251915652091071 / 800000000000
    | 2 => 81464345952543 / 160000000000
    | 3 => 73508358993597 / 800000000000
    | 4 => 197453792062809 / 800000000000
    | 5 => 536125455683253 / 800000000000
    | 6 => 394907584125789 / 800000000000
    | 7 => 676680876383697 / 800000000000
    | 8 => 498440070852723 / 800000000000
    | 9 => 764735248304829 / 800000000000
    | 10 => 441520101467541 / 800000000000
    | 11 => 783485167991769 / 800000000000
    | 12 => 732033474960861 / 800000000000
    | 13 => 522413629224813 / 800000000000
    | 14 => 592361376188427 / 800000000000
    | 15 => 493849158687963 / 800000000000
    | 16 => 436330708643223 / 800000000000
    | 17 => 126465646171077 / 160000000000
    | 18 => 349810632831519 / 800000000000
    | 19 => 296538347497959 / 800000000000
    | 20 => 185559929147277 / 800000000000
    | 21 => 99794747039859 / 800000000000
    | 22 => 270962151056577 / 800000000000
    | 23 => 369975652000929 / 800000000000
    | 24 => 156440070852723 / 800000000000
    | 25 => 635920202723283 / 800000000000
    | _ => 424765224292797 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33053205029 / 1000000000000) (33053205030 / 1000000000000), orderedInterval (19877521176 / 1000000000000) (19877521177 / 1000000000000))
    | 1 => (orderedInterval (44905888253 / 1000000000000) (44905888330 / 1000000000000), orderedInterval (2198168368 / 1000000000000) (2198168444 / 1000000000000))
    | 2 => (orderedInterval (29741395778 / 1000000000000) (29741395779 / 1000000000000), orderedInterval (19096739248 / 1000000000000) (19096739249 / 1000000000000))
    | 3 => (orderedInterval (-83234097157 / 1000000000000) (-83234097129 / 1000000000000), orderedInterval (-171090663 / 1000000000000) (-171090636 / 1000000000000))
    | 4 => (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))
    | 5 => (orderedInterval (-30131340102 / 1000000000000) (-30131326115 / 1000000000000), orderedInterval (6507759486 / 1000000000000) (6507773473 / 1000000000000))
    | 6 => (orderedInterval (-33333774260 / 1000000000000) (-33333774257 / 1000000000000), orderedInterval (-13327271188 / 1000000000000) (-13327271185 / 1000000000000))
    | 7 => (orderedInterval (-27427072918 / 1000000000000) (-27427069798 / 1000000000000), orderedInterval (-611272927 / 1000000000000) (-611269807 / 1000000000000))
    | 8 => (orderedInterval (31129735965 / 1000000000000) (31129749063 / 1000000000000), orderedInterval (-7285722820 / 1000000000000) (-7285709722 / 1000000000000))
    | 9 => (orderedInterval (25703535076 / 1000000000000) (25703552409 / 1000000000000), orderedInterval (-2316578630 / 1000000000000) (-2316561297 / 1000000000000))
    | 10 => (orderedInterval (-7908394876 / 1000000000000) (-7908394869 / 1000000000000), orderedInterval (33036895310 / 1000000000000) (33036895317 / 1000000000000))
    | 11 => (orderedInterval (-896693087 / 1000000000000) (-896693086 / 1000000000000), orderedInterval (25480546139 / 1000000000000) (25480546140 / 1000000000000))
    | 12 => (orderedInterval (-26339826214 / 1000000000000) (-26339816304 / 1000000000000), orderedInterval (1407658778 / 1000000000000) (1407668688 / 1000000000000))
    | 13 => (orderedInterval (10734859237 / 1000000000000) (10734859238 / 1000000000000), orderedInterval (29311620366 / 1000000000000) (29311620367 / 1000000000000))
    | 14 => (orderedInterval (-5218226276 / 1000000000000) (-5218226274 / 1000000000000), orderedInterval (28857335464 / 1000000000000) (28857335466 / 1000000000000))
    | 15 => (orderedInterval (22972036183 / 1000000000000) (22972043259 / 1000000000000), orderedInterval (-22458829923 / 1000000000000) (-22458822846 / 1000000000000))
    | 16 => (orderedInterval (-14507764559 / 1000000000000) (-14507764401 / 1000000000000), orderedInterval (30944665826 / 1000000000000) (30944665984 / 1000000000000))
    | 17 => (orderedInterval (-13251620290 / 1000000000000) (-13251620237 / 1000000000000), orderedInterval (25104680501 / 1000000000000) (25104680555 / 1000000000000))
    | 18 => (orderedInterval (-37367041477 / 1000000000000) (-37367041457 / 1000000000000), orderedInterval (-7678798148 / 1000000000000) (-7678798128 / 1000000000000))
    | 19 => (orderedInterval (28250601124 / 1000000000000) (28250601125 / 1000000000000), orderedInterval (30283073457 / 1000000000000) (30283073458 / 1000000000000))
    | 20 => (orderedInterval (13311978919 / 1000000000000) (13311978920 / 1000000000000), orderedInterval (50641217286 / 1000000000000) (50641217287 / 1000000000000))
    | 21 => (orderedInterval (-9676887736 / 1000000000000) (-9676887692 / 1000000000000), orderedInterval (70818942336 / 1000000000000) (70818942380 / 1000000000000))
    | 22 => (orderedInterval (8430833113 / 1000000000000) (8430833114 / 1000000000000), orderedInterval (42514085002 / 1000000000000) (42514085003 / 1000000000000))
    | 23 => (orderedInterval (-36787941062 / 1000000000000) (-36787940991 / 1000000000000), orderedInterval (-4778150185 / 1000000000000) (-4778150114 / 1000000000000))
    | 24 => (orderedInterval (57051026180 / 1000000000000) (57051026234 / 1000000000000), orderedInterval (692460590 / 1000000000000) (692460644 / 1000000000000))
    | 25 => (orderedInterval (-21493876990 / 1000000000000) (-21493876989 / 1000000000000), orderedInterval (-18395534981 / 1000000000000) (-18395534980 / 1000000000000))
    | _ => (orderedInterval (-25140072929 / 1000000000000) (-25140072928 / 1000000000000), orderedInterval (-23787712722 / 1000000000000) (-23787712721 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15264828135 / 1000000000000) (15264828167 / 1000000000000)
      | 1 => orderedInterval (4066980383 / 1000000000000) (4066981627 / 1000000000000)
      | 2 => orderedInterval (1598304855 / 1000000000000) (1598305293 / 1000000000000)
      | 3 => orderedInterval (-5280628191 / 1000000000000) (-5280624941 / 1000000000000)
      | 4 => orderedInterval (1517041230 / 1000000000000) (1517041460 / 1000000000000)
      | 5 => orderedInterval (756210796 / 1000000000000) (756210930 / 1000000000000)
      | 6 => orderedInterval (4809099756 / 1000000000000) (4809099867 / 1000000000000)
      | 7 => orderedInterval (2806801918 / 1000000000000) (2806801975 / 1000000000000)
      | _ => orderedInterval (6810506593 / 1000000000000) (6810506712 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9228496627 / 1000000000000) (9228496662 / 1000000000000)
      | 1 => orderedInterval (-1619373844 / 1000000000000) (-1619372113 / 1000000000000)
      | 2 => orderedInterval (-219321520 / 1000000000000) (-219320826 / 1000000000000)
      | 3 => orderedInterval (12378560978 / 1000000000000) (12378568217 / 1000000000000)
      | 4 => orderedInterval (3926646080 / 1000000000000) (3926646546 / 1000000000000)
      | 5 => orderedInterval (-1445356324 / 1000000000000) (-1445356132 / 1000000000000)
      | 6 => orderedInterval (664150629 / 1000000000000) (664150732 / 1000000000000)
      | 7 => orderedInterval (-749600874 / 1000000000000) (-749600822 / 1000000000000)
      | _ => orderedInterval (8329570702 / 1000000000000) (8329570869 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15825365888 / 1000000000000) (-15825365848 / 1000000000000)
      | 1 => orderedInterval (-5642444705 / 1000000000000) (-5642442110 / 1000000000000)
      | 2 => orderedInterval (-4909350194 / 1000000000000) (-4909349069 / 1000000000000)
      | 3 => orderedInterval (24452648950 / 1000000000000) (24452665119 / 1000000000000)
      | 4 => orderedInterval (-4635600608 / 1000000000000) (-4635599650 / 1000000000000)
      | 5 => orderedInterval (-741267084 / 1000000000000) (-741266806 / 1000000000000)
      | 6 => orderedInterval (-5177723547 / 1000000000000) (-5177723449 / 1000000000000)
      | 7 => orderedInterval (-3192901555 / 1000000000000) (-3192901503 / 1000000000000)
      | _ => orderedInterval (-13416929490 / 1000000000000) (-13416929244 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9743051893 / 1000000000000) (-9743051847 / 1000000000000)
      | 1 => orderedInterval (2093560003 / 1000000000000) (2093563998 / 1000000000000)
      | 2 => orderedInterval (410536836 / 1000000000000) (410538699 / 1000000000000)
      | 3 => orderedInterval (-53475964877 / 1000000000000) (-53475928755 / 1000000000000)
      | 4 => orderedInterval (-8860395238 / 1000000000000) (-8860393249 / 1000000000000)
      | 5 => orderedInterval (397449136 / 1000000000000) (397449546 / 1000000000000)
      | 6 => orderedInterval (-447725560 / 1000000000000) (-447725464 / 1000000000000)
      | 7 => orderedInterval (56030938 / 1000000000000) (56030992 / 1000000000000)
      | _ => orderedInterval (-18146606151 / 1000000000000) (-18146605772 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16781415524 / 1000000000000) (16781415578 / 1000000000000)
      | 1 => orderedInterval (13041227542 / 1000000000000) (13041233773 / 1000000000000)
      | 2 => orderedInterval (16357722419 / 1000000000000) (16357725580 / 1000000000000)
      | 3 => orderedInterval (-119068563978 / 1000000000000) (-119068483153 / 1000000000000)
      | 4 => orderedInterval (15787068722 / 1000000000000) (15787072889 / 1000000000000)
      | 5 => orderedInterval (-613815236 / 1000000000000) (-613814624 / 1000000000000)
      | 6 => orderedInterval (5675339087 / 1000000000000) (5675339181 / 1000000000000)
      | 7 => orderedInterval (3787031521 / 1000000000000) (3787031578 / 1000000000000)
      | _ => orderedInterval (32238844222 / 1000000000000) (32238844832 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (32349145475 / 1000000000000) (32349151090 / 1000000000000)
    | 1 => orderedInterval (30493772454 / 1000000000000) (30493783133 / 1000000000000)
    | 2 => orderedInterval (-29088934121 / 1000000000000) (-29088912560 / 1000000000000)
    | 3 => orderedInterval (-87716166806 / 1000000000000) (-87716121852 / 1000000000000)
    | _ => orderedInterval (-16013730177 / 1000000000000) (-16013634366 / 1000000000000)

theorem compactCertificate556_stateChecks0 :
    compactCertificate556.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (855 / 2)) (orderedInterval (33053205029 / 1000000000000) (33053205030 / 1000000000000), orderedInterval (19877521176 / 1000000000000) (19877521177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (251915652091071 / 800000000000)) (orderedInterval (44905888253 / 1000000000000) (44905888330 / 1000000000000), orderedInterval (2198168368 / 1000000000000) (2198168444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (81464345952543 / 160000000000)) (orderedInterval (29741395778 / 1000000000000) (29741395779 / 1000000000000), orderedInterval (19096739248 / 1000000000000) (19096739249 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks1 :
    compactCertificate556.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (73508358993597 / 800000000000)) (orderedInterval (-83234097157 / 1000000000000) (-83234097129 / 1000000000000), orderedInterval (-171090663 / 1000000000000) (-171090636 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (197453792062809 / 800000000000)) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (536125455683253 / 800000000000)) (orderedInterval (-30131340102 / 1000000000000) (-30131326115 / 1000000000000), orderedInterval (6507759486 / 1000000000000) (6507773473 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks2 :
    compactCertificate556.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (394907584125789 / 800000000000)) (orderedInterval (-33333774260 / 1000000000000) (-33333774257 / 1000000000000), orderedInterval (-13327271188 / 1000000000000) (-13327271185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (676680876383697 / 800000000000)) (orderedInterval (-27427072918 / 1000000000000) (-27427069798 / 1000000000000), orderedInterval (-611272927 / 1000000000000) (-611269807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (498440070852723 / 800000000000)) (orderedInterval (31129735965 / 1000000000000) (31129749063 / 1000000000000), orderedInterval (-7285722820 / 1000000000000) (-7285709722 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks3 :
    compactCertificate556.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 304 12 (764735248304829 / 800000000000)) (orderedInterval (25703535076 / 1000000000000) (25703552409 / 1000000000000), orderedInterval (-2316578630 / 1000000000000) (-2316561297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (441520101467541 / 800000000000)) (orderedInterval (-7908394876 / 1000000000000) (-7908394869 / 1000000000000), orderedInterval (33036895310 / 1000000000000) (33036895317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 312 12 (783485167991769 / 800000000000)) (orderedInterval (-896693087 / 1000000000000) (-896693086 / 1000000000000), orderedInterval (25480546139 / 1000000000000) (25480546140 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks4 :
    compactCertificate556.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (732033474960861 / 800000000000)) (orderedInterval (-26339826214 / 1000000000000) (-26339816304 / 1000000000000), orderedInterval (1407658778 / 1000000000000) (1407668688 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (522413629224813 / 800000000000)) (orderedInterval (10734859237 / 1000000000000) (10734859238 / 1000000000000), orderedInterval (29311620366 / 1000000000000) (29311620367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (592361376188427 / 800000000000)) (orderedInterval (-5218226276 / 1000000000000) (-5218226274 / 1000000000000), orderedInterval (28857335464 / 1000000000000) (28857335466 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks5 :
    compactCertificate556.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (493849158687963 / 800000000000)) (orderedInterval (22972036183 / 1000000000000) (22972043259 / 1000000000000), orderedInterval (-22458829923 / 1000000000000) (-22458822846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (436330708643223 / 800000000000)) (orderedInterval (-14507764559 / 1000000000000) (-14507764401 / 1000000000000), orderedInterval (30944665826 / 1000000000000) (30944665984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (126465646171077 / 160000000000)) (orderedInterval (-13251620290 / 1000000000000) (-13251620237 / 1000000000000), orderedInterval (25104680501 / 1000000000000) (25104680555 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks6 :
    compactCertificate556.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (349810632831519 / 800000000000)) (orderedInterval (-37367041477 / 1000000000000) (-37367041457 / 1000000000000), orderedInterval (-7678798148 / 1000000000000) (-7678798128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (296538347497959 / 800000000000)) (orderedInterval (28250601124 / 1000000000000) (28250601125 / 1000000000000), orderedInterval (30283073457 / 1000000000000) (30283073458 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (185559929147277 / 800000000000)) (orderedInterval (13311978919 / 1000000000000) (13311978920 / 1000000000000), orderedInterval (50641217286 / 1000000000000) (50641217287 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks7 :
    compactCertificate556.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (99794747039859 / 800000000000)) (orderedInterval (-9676887736 / 1000000000000) (-9676887692 / 1000000000000), orderedInterval (70818942336 / 1000000000000) (70818942380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (270962151056577 / 800000000000)) (orderedInterval (8430833113 / 1000000000000) (8430833114 / 1000000000000), orderedInterval (42514085002 / 1000000000000) (42514085003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (369975652000929 / 800000000000)) (orderedInterval (-36787941062 / 1000000000000) (-36787940991 / 1000000000000), orderedInterval (-4778150185 / 1000000000000) (-4778150114 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_stateChecks8 :
    compactCertificate556.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (156440070852723 / 800000000000)) (orderedInterval (57051026180 / 1000000000000) (57051026234 / 1000000000000), orderedInterval (692460590 / 1000000000000) (692460644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (635920202723283 / 800000000000)) (orderedInterval (-21493876990 / 1000000000000) (-21493876989 / 1000000000000), orderedInterval (-18395534981 / 1000000000000) (-18395534980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (424765224292797 / 800000000000)) (orderedInterval (-25140072929 / 1000000000000) (-25140072928 / 1000000000000), orderedInterval (-23787712722 / 1000000000000) (-23787712721 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_states : ∀ j,
    BesselStateValid (compactCertificate556.point j) (compactCertificate556.state j) :=
  compactCertificate556.statesValid_of_checks3 compactCertificate556_stateChecks0
    compactCertificate556_stateChecks1 compactCertificate556_stateChecks2
    compactCertificate556_stateChecks3 compactCertificate556_stateChecks4
    compactCertificate556_stateChecks5 compactCertificate556_stateChecks6
    compactCertificate556_stateChecks7 compactCertificate556_stateChecks8

theorem compactCertificate556_chunkChecks0_0 :
    compactCertificate556.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (855 / 2) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33053205029 / 1000000000000) (33053205030 / 1000000000000), orderedInterval (19877521176 / 1000000000000) (19877521177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (251915652091071 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44905888253 / 1000000000000) (44905888330 / 1000000000000), orderedInterval (2198168368 / 1000000000000) (2198168444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (81464345952543 / 160000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29741395778 / 1000000000000) (29741395779 / 1000000000000), orderedInterval (19096739248 / 1000000000000) (19096739249 / 1000000000000)))) (orderedInterval (15264828135 / 1000000000000) (15264828167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (73508358993597 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83234097157 / 1000000000000) (-83234097129 / 1000000000000), orderedInterval (-171090663 / 1000000000000) (-171090636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (536125455683253 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30131340102 / 1000000000000) (-30131326115 / 1000000000000), orderedInterval (6507759486 / 1000000000000) (6507773473 / 1000000000000)))) (orderedInterval (4066980383 / 1000000000000) (4066981627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (394907584125789 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33333774260 / 1000000000000) (-33333774257 / 1000000000000), orderedInterval (-13327271188 / 1000000000000) (-13327271185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (676680876383697 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27427072918 / 1000000000000) (-27427069798 / 1000000000000), orderedInterval (-611272927 / 1000000000000) (-611269807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (498440070852723 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31129735965 / 1000000000000) (31129749063 / 1000000000000), orderedInterval (-7285722820 / 1000000000000) (-7285709722 / 1000000000000)))) (orderedInterval (1598304855 / 1000000000000) (1598305293 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks0_1 :
    compactCertificate556.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (764735248304829 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25703535076 / 1000000000000) (25703552409 / 1000000000000), orderedInterval (-2316578630 / 1000000000000) (-2316561297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (441520101467541 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7908394876 / 1000000000000) (-7908394869 / 1000000000000), orderedInterval (33036895310 / 1000000000000) (33036895317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (783485167991769 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-896693087 / 1000000000000) (-896693086 / 1000000000000), orderedInterval (25480546139 / 1000000000000) (25480546140 / 1000000000000)))) (orderedInterval (-5280628191 / 1000000000000) (-5280624941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (732033474960861 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26339826214 / 1000000000000) (-26339816304 / 1000000000000), orderedInterval (1407658778 / 1000000000000) (1407668688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (522413629224813 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10734859237 / 1000000000000) (10734859238 / 1000000000000), orderedInterval (29311620366 / 1000000000000) (29311620367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (592361376188427 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5218226276 / 1000000000000) (-5218226274 / 1000000000000), orderedInterval (28857335464 / 1000000000000) (28857335466 / 1000000000000)))) (orderedInterval (1517041230 / 1000000000000) (1517041460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (493849158687963 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22972036183 / 1000000000000) (22972043259 / 1000000000000), orderedInterval (-22458829923 / 1000000000000) (-22458822846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (436330708643223 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14507764559 / 1000000000000) (-14507764401 / 1000000000000), orderedInterval (30944665826 / 1000000000000) (30944665984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (126465646171077 / 160000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13251620290 / 1000000000000) (-13251620237 / 1000000000000), orderedInterval (25104680501 / 1000000000000) (25104680555 / 1000000000000)))) (orderedInterval (756210796 / 1000000000000) (756210930 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks0_2 :
    compactCertificate556.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (349810632831519 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37367041477 / 1000000000000) (-37367041457 / 1000000000000), orderedInterval (-7678798148 / 1000000000000) (-7678798128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (296538347497959 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28250601124 / 1000000000000) (28250601125 / 1000000000000), orderedInterval (30283073457 / 1000000000000) (30283073458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (185559929147277 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13311978919 / 1000000000000) (13311978920 / 1000000000000), orderedInterval (50641217286 / 1000000000000) (50641217287 / 1000000000000)))) (orderedInterval (4809099756 / 1000000000000) (4809099867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (99794747039859 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9676887736 / 1000000000000) (-9676887692 / 1000000000000), orderedInterval (70818942336 / 1000000000000) (70818942380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (270962151056577 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8430833113 / 1000000000000) (8430833114 / 1000000000000), orderedInterval (42514085002 / 1000000000000) (42514085003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (369975652000929 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36787941062 / 1000000000000) (-36787940991 / 1000000000000), orderedInterval (-4778150185 / 1000000000000) (-4778150114 / 1000000000000)))) (orderedInterval (2806801918 / 1000000000000) (2806801975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (156440070852723 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57051026180 / 1000000000000) (57051026234 / 1000000000000), orderedInterval (692460590 / 1000000000000) (692460644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (635920202723283 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21493876990 / 1000000000000) (-21493876989 / 1000000000000), orderedInterval (-18395534981 / 1000000000000) (-18395534980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (424765224292797 / 800000000000) 0 (IntervalRat.scale (855 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25140072929 / 1000000000000) (-25140072928 / 1000000000000), orderedInterval (-23787712722 / 1000000000000) (-23787712721 / 1000000000000)))) (orderedInterval (6810506593 / 1000000000000) (6810506712 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks0 :
    compactCertificate556.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate556.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate556_chunkChecks0_0
    compactCertificate556_chunkChecks0_1 compactCertificate556_chunkChecks0_2

theorem compactCertificate556_chunkChecks1_0 :
    compactCertificate556.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (855 / 2) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33053205029 / 1000000000000) (33053205030 / 1000000000000), orderedInterval (19877521176 / 1000000000000) (19877521177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (251915652091071 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44905888253 / 1000000000000) (44905888330 / 1000000000000), orderedInterval (2198168368 / 1000000000000) (2198168444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (81464345952543 / 160000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29741395778 / 1000000000000) (29741395779 / 1000000000000), orderedInterval (19096739248 / 1000000000000) (19096739249 / 1000000000000)))) (orderedInterval (9228496627 / 1000000000000) (9228496662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (73508358993597 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83234097157 / 1000000000000) (-83234097129 / 1000000000000), orderedInterval (-171090663 / 1000000000000) (-171090636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (536125455683253 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30131340102 / 1000000000000) (-30131326115 / 1000000000000), orderedInterval (6507759486 / 1000000000000) (6507773473 / 1000000000000)))) (orderedInterval (-1619373844 / 1000000000000) (-1619372113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (394907584125789 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33333774260 / 1000000000000) (-33333774257 / 1000000000000), orderedInterval (-13327271188 / 1000000000000) (-13327271185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (676680876383697 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27427072918 / 1000000000000) (-27427069798 / 1000000000000), orderedInterval (-611272927 / 1000000000000) (-611269807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (498440070852723 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31129735965 / 1000000000000) (31129749063 / 1000000000000), orderedInterval (-7285722820 / 1000000000000) (-7285709722 / 1000000000000)))) (orderedInterval (-219321520 / 1000000000000) (-219320826 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks1_1 :
    compactCertificate556.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (764735248304829 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25703535076 / 1000000000000) (25703552409 / 1000000000000), orderedInterval (-2316578630 / 1000000000000) (-2316561297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (441520101467541 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7908394876 / 1000000000000) (-7908394869 / 1000000000000), orderedInterval (33036895310 / 1000000000000) (33036895317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (783485167991769 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-896693087 / 1000000000000) (-896693086 / 1000000000000), orderedInterval (25480546139 / 1000000000000) (25480546140 / 1000000000000)))) (orderedInterval (12378560978 / 1000000000000) (12378568217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (732033474960861 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26339826214 / 1000000000000) (-26339816304 / 1000000000000), orderedInterval (1407658778 / 1000000000000) (1407668688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (522413629224813 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10734859237 / 1000000000000) (10734859238 / 1000000000000), orderedInterval (29311620366 / 1000000000000) (29311620367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (592361376188427 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5218226276 / 1000000000000) (-5218226274 / 1000000000000), orderedInterval (28857335464 / 1000000000000) (28857335466 / 1000000000000)))) (orderedInterval (3926646080 / 1000000000000) (3926646546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (493849158687963 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22972036183 / 1000000000000) (22972043259 / 1000000000000), orderedInterval (-22458829923 / 1000000000000) (-22458822846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (436330708643223 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14507764559 / 1000000000000) (-14507764401 / 1000000000000), orderedInterval (30944665826 / 1000000000000) (30944665984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (126465646171077 / 160000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13251620290 / 1000000000000) (-13251620237 / 1000000000000), orderedInterval (25104680501 / 1000000000000) (25104680555 / 1000000000000)))) (orderedInterval (-1445356324 / 1000000000000) (-1445356132 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks1_2 :
    compactCertificate556.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (349810632831519 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37367041477 / 1000000000000) (-37367041457 / 1000000000000), orderedInterval (-7678798148 / 1000000000000) (-7678798128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (296538347497959 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28250601124 / 1000000000000) (28250601125 / 1000000000000), orderedInterval (30283073457 / 1000000000000) (30283073458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (185559929147277 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13311978919 / 1000000000000) (13311978920 / 1000000000000), orderedInterval (50641217286 / 1000000000000) (50641217287 / 1000000000000)))) (orderedInterval (664150629 / 1000000000000) (664150732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (99794747039859 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9676887736 / 1000000000000) (-9676887692 / 1000000000000), orderedInterval (70818942336 / 1000000000000) (70818942380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (270962151056577 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8430833113 / 1000000000000) (8430833114 / 1000000000000), orderedInterval (42514085002 / 1000000000000) (42514085003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (369975652000929 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36787941062 / 1000000000000) (-36787940991 / 1000000000000), orderedInterval (-4778150185 / 1000000000000) (-4778150114 / 1000000000000)))) (orderedInterval (-749600874 / 1000000000000) (-749600822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (156440070852723 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57051026180 / 1000000000000) (57051026234 / 1000000000000), orderedInterval (692460590 / 1000000000000) (692460644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (635920202723283 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21493876990 / 1000000000000) (-21493876989 / 1000000000000), orderedInterval (-18395534981 / 1000000000000) (-18395534980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (424765224292797 / 800000000000) 1 (IntervalRat.scale (855 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25140072929 / 1000000000000) (-25140072928 / 1000000000000), orderedInterval (-23787712722 / 1000000000000) (-23787712721 / 1000000000000)))) (orderedInterval (8329570702 / 1000000000000) (8329570869 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks1 :
    compactCertificate556.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate556.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate556_chunkChecks1_0
    compactCertificate556_chunkChecks1_1 compactCertificate556_chunkChecks1_2

theorem compactCertificate556_chunkChecks2_0 :
    compactCertificate556.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (855 / 2) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33053205029 / 1000000000000) (33053205030 / 1000000000000), orderedInterval (19877521176 / 1000000000000) (19877521177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (251915652091071 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44905888253 / 1000000000000) (44905888330 / 1000000000000), orderedInterval (2198168368 / 1000000000000) (2198168444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (81464345952543 / 160000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29741395778 / 1000000000000) (29741395779 / 1000000000000), orderedInterval (19096739248 / 1000000000000) (19096739249 / 1000000000000)))) (orderedInterval (-15825365888 / 1000000000000) (-15825365848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (73508358993597 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83234097157 / 1000000000000) (-83234097129 / 1000000000000), orderedInterval (-171090663 / 1000000000000) (-171090636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (536125455683253 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30131340102 / 1000000000000) (-30131326115 / 1000000000000), orderedInterval (6507759486 / 1000000000000) (6507773473 / 1000000000000)))) (orderedInterval (-5642444705 / 1000000000000) (-5642442110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (394907584125789 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33333774260 / 1000000000000) (-33333774257 / 1000000000000), orderedInterval (-13327271188 / 1000000000000) (-13327271185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (676680876383697 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27427072918 / 1000000000000) (-27427069798 / 1000000000000), orderedInterval (-611272927 / 1000000000000) (-611269807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (498440070852723 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31129735965 / 1000000000000) (31129749063 / 1000000000000), orderedInterval (-7285722820 / 1000000000000) (-7285709722 / 1000000000000)))) (orderedInterval (-4909350194 / 1000000000000) (-4909349069 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks2_1 :
    compactCertificate556.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (764735248304829 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25703535076 / 1000000000000) (25703552409 / 1000000000000), orderedInterval (-2316578630 / 1000000000000) (-2316561297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (441520101467541 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7908394876 / 1000000000000) (-7908394869 / 1000000000000), orderedInterval (33036895310 / 1000000000000) (33036895317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (783485167991769 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-896693087 / 1000000000000) (-896693086 / 1000000000000), orderedInterval (25480546139 / 1000000000000) (25480546140 / 1000000000000)))) (orderedInterval (24452648950 / 1000000000000) (24452665119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (732033474960861 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26339826214 / 1000000000000) (-26339816304 / 1000000000000), orderedInterval (1407658778 / 1000000000000) (1407668688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (522413629224813 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10734859237 / 1000000000000) (10734859238 / 1000000000000), orderedInterval (29311620366 / 1000000000000) (29311620367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (592361376188427 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5218226276 / 1000000000000) (-5218226274 / 1000000000000), orderedInterval (28857335464 / 1000000000000) (28857335466 / 1000000000000)))) (orderedInterval (-4635600608 / 1000000000000) (-4635599650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (493849158687963 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22972036183 / 1000000000000) (22972043259 / 1000000000000), orderedInterval (-22458829923 / 1000000000000) (-22458822846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (436330708643223 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14507764559 / 1000000000000) (-14507764401 / 1000000000000), orderedInterval (30944665826 / 1000000000000) (30944665984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (126465646171077 / 160000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13251620290 / 1000000000000) (-13251620237 / 1000000000000), orderedInterval (25104680501 / 1000000000000) (25104680555 / 1000000000000)))) (orderedInterval (-741267084 / 1000000000000) (-741266806 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks2_2 :
    compactCertificate556.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (349810632831519 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37367041477 / 1000000000000) (-37367041457 / 1000000000000), orderedInterval (-7678798148 / 1000000000000) (-7678798128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (296538347497959 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28250601124 / 1000000000000) (28250601125 / 1000000000000), orderedInterval (30283073457 / 1000000000000) (30283073458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (185559929147277 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13311978919 / 1000000000000) (13311978920 / 1000000000000), orderedInterval (50641217286 / 1000000000000) (50641217287 / 1000000000000)))) (orderedInterval (-5177723547 / 1000000000000) (-5177723449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (99794747039859 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9676887736 / 1000000000000) (-9676887692 / 1000000000000), orderedInterval (70818942336 / 1000000000000) (70818942380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (270962151056577 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8430833113 / 1000000000000) (8430833114 / 1000000000000), orderedInterval (42514085002 / 1000000000000) (42514085003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (369975652000929 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36787941062 / 1000000000000) (-36787940991 / 1000000000000), orderedInterval (-4778150185 / 1000000000000) (-4778150114 / 1000000000000)))) (orderedInterval (-3192901555 / 1000000000000) (-3192901503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (156440070852723 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57051026180 / 1000000000000) (57051026234 / 1000000000000), orderedInterval (692460590 / 1000000000000) (692460644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (635920202723283 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21493876990 / 1000000000000) (-21493876989 / 1000000000000), orderedInterval (-18395534981 / 1000000000000) (-18395534980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (424765224292797 / 800000000000) 2 (IntervalRat.scale (855 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25140072929 / 1000000000000) (-25140072928 / 1000000000000), orderedInterval (-23787712722 / 1000000000000) (-23787712721 / 1000000000000)))) (orderedInterval (-13416929490 / 1000000000000) (-13416929244 / 1000000000000))) = true
  rfl'

theorem compactCertificate556_chunkChecks2 :
    compactCertificate556.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate556.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate556_chunkChecks2_0
    compactCertificate556_chunkChecks2_1 compactCertificate556_chunkChecks2_2

theorem compactCertificate556_chunkChecks3_0 :
    compactCertificate556.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (855 / 2) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33053205029 / 1000000000000) (33053205030 / 1000000000000), orderedInterval (19877521176 / 1000000000000) (19877521177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (251915652091071 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44905888253 / 1000000000000) (44905888330 / 1000000000000), orderedInterval (2198168368 / 1000000000000) (2198168444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (81464345952543 / 160000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29741395778 / 1000000000000) (29741395779 / 1000000000000), orderedInterval (19096739248 / 1000000000000) (19096739249 / 1000000000000)))) (orderedInterval (-9743051893 / 1000000000000) (-9743051847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (73508358993597 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83234097157 / 1000000000000) (-83234097129 / 1000000000000), orderedInterval (-171090663 / 1000000000000) (-171090636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (536125455683253 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30131340102 / 1000000000000) (-30131326115 / 1000000000000), orderedInterval (6507759486 / 1000000000000) (6507773473 / 1000000000000)))) (orderedInterval (2093560003 / 1000000000000) (2093563998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (394907584125789 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33333774260 / 1000000000000) (-33333774257 / 1000000000000), orderedInterval (-13327271188 / 1000000000000) (-13327271185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (676680876383697 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27427072918 / 1000000000000) (-27427069798 / 1000000000000), orderedInterval (-611272927 / 1000000000000) (-611269807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (498440070852723 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31129735965 / 1000000000000) (31129749063 / 1000000000000), orderedInterval (-7285722820 / 1000000000000) (-7285709722 / 1000000000000)))) (orderedInterval (410536836 / 1000000000000) (410538699 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate556_chunkChecks3_1 :
    compactCertificate556.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (764735248304829 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25703535076 / 1000000000000) (25703552409 / 1000000000000), orderedInterval (-2316578630 / 1000000000000) (-2316561297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (441520101467541 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7908394876 / 1000000000000) (-7908394869 / 1000000000000), orderedInterval (33036895310 / 1000000000000) (33036895317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (783485167991769 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-896693087 / 1000000000000) (-896693086 / 1000000000000), orderedInterval (25480546139 / 1000000000000) (25480546140 / 1000000000000)))) (orderedInterval (-53475964877 / 1000000000000) (-53475928755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (732033474960861 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26339826214 / 1000000000000) (-26339816304 / 1000000000000), orderedInterval (1407658778 / 1000000000000) (1407668688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (522413629224813 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10734859237 / 1000000000000) (10734859238 / 1000000000000), orderedInterval (29311620366 / 1000000000000) (29311620367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (592361376188427 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5218226276 / 1000000000000) (-5218226274 / 1000000000000), orderedInterval (28857335464 / 1000000000000) (28857335466 / 1000000000000)))) (orderedInterval (-8860395238 / 1000000000000) (-8860393249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (493849158687963 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22972036183 / 1000000000000) (22972043259 / 1000000000000), orderedInterval (-22458829923 / 1000000000000) (-22458822846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (436330708643223 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14507764559 / 1000000000000) (-14507764401 / 1000000000000), orderedInterval (30944665826 / 1000000000000) (30944665984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (126465646171077 / 160000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13251620290 / 1000000000000) (-13251620237 / 1000000000000), orderedInterval (25104680501 / 1000000000000) (25104680555 / 1000000000000)))) (orderedInterval (397449136 / 1000000000000) (397449546 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate556_chunkChecks3_2 :
    compactCertificate556.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (349810632831519 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37367041477 / 1000000000000) (-37367041457 / 1000000000000), orderedInterval (-7678798148 / 1000000000000) (-7678798128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (296538347497959 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28250601124 / 1000000000000) (28250601125 / 1000000000000), orderedInterval (30283073457 / 1000000000000) (30283073458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (185559929147277 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13311978919 / 1000000000000) (13311978920 / 1000000000000), orderedInterval (50641217286 / 1000000000000) (50641217287 / 1000000000000)))) (orderedInterval (-447725560 / 1000000000000) (-447725464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (99794747039859 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9676887736 / 1000000000000) (-9676887692 / 1000000000000), orderedInterval (70818942336 / 1000000000000) (70818942380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (270962151056577 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8430833113 / 1000000000000) (8430833114 / 1000000000000), orderedInterval (42514085002 / 1000000000000) (42514085003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (369975652000929 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36787941062 / 1000000000000) (-36787940991 / 1000000000000), orderedInterval (-4778150185 / 1000000000000) (-4778150114 / 1000000000000)))) (orderedInterval (56030938 / 1000000000000) (56030992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (156440070852723 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57051026180 / 1000000000000) (57051026234 / 1000000000000), orderedInterval (692460590 / 1000000000000) (692460644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (635920202723283 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21493876990 / 1000000000000) (-21493876989 / 1000000000000), orderedInterval (-18395534981 / 1000000000000) (-18395534980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (424765224292797 / 800000000000) 3 (IntervalRat.scale (855 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25140072929 / 1000000000000) (-25140072928 / 1000000000000), orderedInterval (-23787712722 / 1000000000000) (-23787712721 / 1000000000000)))) (orderedInterval (-18146606151 / 1000000000000) (-18146605772 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate556_chunkChecks3 :
    compactCertificate556.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate556.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate556_chunkChecks3_0
    compactCertificate556_chunkChecks3_1 compactCertificate556_chunkChecks3_2

theorem compactCertificate556_chunkChecks4_0 :
    compactCertificate556.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (855 / 2) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33053205029 / 1000000000000) (33053205030 / 1000000000000), orderedInterval (19877521176 / 1000000000000) (19877521177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (251915652091071 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44905888253 / 1000000000000) (44905888330 / 1000000000000), orderedInterval (2198168368 / 1000000000000) (2198168444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (81464345952543 / 160000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29741395778 / 1000000000000) (29741395779 / 1000000000000), orderedInterval (19096739248 / 1000000000000) (19096739249 / 1000000000000)))) (orderedInterval (16781415524 / 1000000000000) (16781415578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (73508358993597 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83234097157 / 1000000000000) (-83234097129 / 1000000000000), orderedInterval (-171090663 / 1000000000000) (-171090636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (197453792062809 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27988919291 / 1000000000000) (27988924709 / 1000000000000), orderedInterval (-42435220072 / 1000000000000) (-42435214654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (536125455683253 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30131340102 / 1000000000000) (-30131326115 / 1000000000000), orderedInterval (6507759486 / 1000000000000) (6507773473 / 1000000000000)))) (orderedInterval (13041227542 / 1000000000000) (13041233773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (394907584125789 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33333774260 / 1000000000000) (-33333774257 / 1000000000000), orderedInterval (-13327271188 / 1000000000000) (-13327271185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (676680876383697 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27427072918 / 1000000000000) (-27427069798 / 1000000000000), orderedInterval (-611272927 / 1000000000000) (-611269807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (498440070852723 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31129735965 / 1000000000000) (31129749063 / 1000000000000), orderedInterval (-7285722820 / 1000000000000) (-7285709722 / 1000000000000)))) (orderedInterval (16357722419 / 1000000000000) (16357725580 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate556_chunkChecks4_1 :
    compactCertificate556.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (764735248304829 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25703535076 / 1000000000000) (25703552409 / 1000000000000), orderedInterval (-2316578630 / 1000000000000) (-2316561297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (441520101467541 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7908394876 / 1000000000000) (-7908394869 / 1000000000000), orderedInterval (33036895310 / 1000000000000) (33036895317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (783485167991769 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-896693087 / 1000000000000) (-896693086 / 1000000000000), orderedInterval (25480546139 / 1000000000000) (25480546140 / 1000000000000)))) (orderedInterval (-119068563978 / 1000000000000) (-119068483153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (732033474960861 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26339826214 / 1000000000000) (-26339816304 / 1000000000000), orderedInterval (1407658778 / 1000000000000) (1407668688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (522413629224813 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10734859237 / 1000000000000) (10734859238 / 1000000000000), orderedInterval (29311620366 / 1000000000000) (29311620367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (592361376188427 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5218226276 / 1000000000000) (-5218226274 / 1000000000000), orderedInterval (28857335464 / 1000000000000) (28857335466 / 1000000000000)))) (orderedInterval (15787068722 / 1000000000000) (15787072889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (493849158687963 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22972036183 / 1000000000000) (22972043259 / 1000000000000), orderedInterval (-22458829923 / 1000000000000) (-22458822846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (436330708643223 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14507764559 / 1000000000000) (-14507764401 / 1000000000000), orderedInterval (30944665826 / 1000000000000) (30944665984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (126465646171077 / 160000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13251620290 / 1000000000000) (-13251620237 / 1000000000000), orderedInterval (25104680501 / 1000000000000) (25104680555 / 1000000000000)))) (orderedInterval (-613815236 / 1000000000000) (-613814624 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate556_chunkChecks4_2 :
    compactCertificate556.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (349810632831519 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37367041477 / 1000000000000) (-37367041457 / 1000000000000), orderedInterval (-7678798148 / 1000000000000) (-7678798128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (296538347497959 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28250601124 / 1000000000000) (28250601125 / 1000000000000), orderedInterval (30283073457 / 1000000000000) (30283073458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (185559929147277 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (13311978919 / 1000000000000) (13311978920 / 1000000000000), orderedInterval (50641217286 / 1000000000000) (50641217287 / 1000000000000)))) (orderedInterval (5675339087 / 1000000000000) (5675339181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (99794747039859 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9676887736 / 1000000000000) (-9676887692 / 1000000000000), orderedInterval (70818942336 / 1000000000000) (70818942380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (270962151056577 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8430833113 / 1000000000000) (8430833114 / 1000000000000), orderedInterval (42514085002 / 1000000000000) (42514085003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (369975652000929 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36787941062 / 1000000000000) (-36787940991 / 1000000000000), orderedInterval (-4778150185 / 1000000000000) (-4778150114 / 1000000000000)))) (orderedInterval (3787031521 / 1000000000000) (3787031578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (156440070852723 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57051026180 / 1000000000000) (57051026234 / 1000000000000), orderedInterval (692460590 / 1000000000000) (692460644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (635920202723283 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21493876990 / 1000000000000) (-21493876989 / 1000000000000), orderedInterval (-18395534981 / 1000000000000) (-18395534980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (424765224292797 / 800000000000) 4 (IntervalRat.scale (855 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25140072929 / 1000000000000) (-25140072928 / 1000000000000), orderedInterval (-23787712722 / 1000000000000) (-23787712721 / 1000000000000)))) (orderedInterval (32238844222 / 1000000000000) (32238844832 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate556_chunkChecks4 :
    compactCertificate556.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate556.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate556_chunkChecks4_0
    compactCertificate556_chunkChecks4_1 compactCertificate556_chunkChecks4_2

theorem compactCertificate556_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate556.chunkCheck r b = true :=
  compactCertificate556.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate556_chunkChecks0
    · exact compactCertificate556_chunkChecks1
    · exact compactCertificate556_chunkChecks2
    · exact compactCertificate556_chunkChecks3
    · exact compactCertificate556_chunkChecks4)

theorem compactCertificate556_coefficient0 :
    compactCertificate556.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate556_coefficient1 :
    compactCertificate556.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate556_coefficient2 :
    compactCertificate556.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate556_coefficient3 :
    compactCertificate556.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate556_coefficient4 :
    compactCertificate556.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate556_coefficients : ∀ r : Fin 5,
    compactCertificate556.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate556_coefficient0
  · exact compactCertificate556_coefficient1
  · exact compactCertificate556_coefficient2
  · exact compactCertificate556_coefficient3
  · exact compactCertificate556_coefficient4

theorem compactCertificate556_lower : (1 : ℚ) ≤ compactCertificate556.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate556, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate556_proves {t : ℝ} (ht : t ∈ compactCertificate556.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate556.proves compactCertificate556_states compactCertificate556_chunks
    compactCertificate556_coefficients compactCertificate556_lower ht

end Erdos232
