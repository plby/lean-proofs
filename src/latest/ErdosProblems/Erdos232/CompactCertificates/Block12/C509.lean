/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate509 : CompactCertificate where
  left := 380
  right := 381
  center := 761 / 2
  grid := fun i =>
    match i.val with
    | 0 => 121
    | 1 => 89
    | 2 => 144
    | 3 => 26
    | 4 => 70
    | 5 => 190
    | 6 => 140
    | 7 => 240
    | 8 => 177
    | 9 => 271
    | 10 => 156
    | 11 => 278
    | 12 => 259
    | 13 => 185
    | 14 => 210
    | 15 => 175
    | 16 => 155
    | 17 => 224
    | 18 => 124
    | 19 => 105
    | 20 => 66
    | 21 => 35
    | 22 => 96
    | 23 => 131
    | 24 => 55
    | 25 => 225
    | _ => 151
  point := fun i =>
    match i.val with
    | 0 => 761 / 2
    | 1 => 1121098311352661 / 4000000000000
    | 2 => 362540159473013 / 800000000000
    | 3 => 327133691193727 / 4000000000000
    | 4 => 878727109706419 / 4000000000000
    | 5 => 2385915039619623 / 4000000000000
    | 6 => 1757454219413599 / 4000000000000
    | 7 => 3011427759812827 / 4000000000000
    | 8 => 2218204058005393 / 4000000000000
    | 9 => 3403295461754239 / 4000000000000
    | 10 => 1964893550975431 / 4000000000000
    | 11 => 3486738086793779 / 4000000000000
    | 12 => 3257763008451551 / 4000000000000
    | 13 => 2324893402573583 / 4000000000000
    | 14 => 2636181329119257 / 4000000000000
    | 15 => 2197773156500233 / 4000000000000
    | 16 => 1941799235540893 / 4000000000000
    | 17 => 562809103720407 / 800000000000
    | 18 => 1556759599911029 / 4000000000000
    | 19 => 1319682353485069 / 4000000000000
    | 20 => 825795941994607 / 4000000000000
    | 21 => 444115804077969 / 4000000000000
    | 22 => 1205860800900907 / 4000000000000
    | 23 => 1646499831419339 / 4000000000000
    | 24 => 696204058005393 / 4000000000000
    | 25 => 2830030843698353 / 4000000000000
    | _ => 1890329448460927 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-37374722544 / 1000000000000) (-37374722543 / 1000000000000), orderedInterval (-16571443157 / 1000000000000) (-16571443156 / 1000000000000))
    | 1 => (orderedInterval (-47355297910 / 1000000000000) (-47355297886 / 1000000000000), orderedInterval (-5290169266 / 1000000000000) (-5290169243 / 1000000000000))
    | 2 => (orderedInterval (37480627434 / 1000000000000) (37480627826 / 1000000000000), orderedInterval (-48221078 / 1000000000000) (-48220686 / 1000000000000))
    | 3 => (orderedInterval (68329835068 / 1000000000000) (68329835069 / 1000000000000), orderedInterval (55396422149 / 1000000000000) (55396422150 / 1000000000000))
    | 4 => (orderedInterval (28372068676 / 1000000000000) (28372068677 / 1000000000000), orderedInterval (45684163007 / 1000000000000) (45684163008 / 1000000000000))
    | 5 => (orderedInterval (11549715869 / 1000000000000) (11549715870 / 1000000000000), orderedInterval (30550111912 / 1000000000000) (30550111913 / 1000000000000))
    | 6 => (orderedInterval (12179686952 / 1000000000000) (12179686953 / 1000000000000), orderedInterval (36050179138 / 1000000000000) (36050179139 / 1000000000000))
    | 7 => (orderedInterval (-9699343426 / 1000000000000) (-9699343418 / 1000000000000), orderedInterval (27420454904 / 1000000000000) (27420454912 / 1000000000000))
    | 8 => (orderedInterval (22486424065 / 1000000000000) (22486428752 / 1000000000000), orderedInterval (-25364941620 / 1000000000000) (-25364936933 / 1000000000000))
    | 9 => (orderedInterval (-6435863876 / 1000000000000) (-6435863875 / 1000000000000), orderedInterval (-26582285189 / 1000000000000) (-26582285188 / 1000000000000))
    | 10 => (orderedInterval (33826110153 / 1000000000000) (33826131983 / 1000000000000), orderedInterval (-12354397173 / 1000000000000) (-12354375344 / 1000000000000))
    | 11 => (orderedInterval (-21050724406 / 1000000000000) (-21050719386 / 1000000000000), orderedInterval (16959043926 / 1000000000000) (16959048946 / 1000000000000))
    | 12 => (orderedInterval (-27954087758 / 1000000000000) (-27954084972 / 1000000000000), orderedInterval (-466404723 / 1000000000000) (-466401938 / 1000000000000))
    | 13 => (orderedInterval (-24059268672 / 1000000000000) (-24059268671 / 1000000000000), orderedInterval (-22705094647 / 1000000000000) (-22705094646 / 1000000000000))
    | 14 => (orderedInterval (2981692289 / 1000000000000) (2981692290 / 1000000000000), orderedInterval (30934486949 / 1000000000000) (30934486950 / 1000000000000))
    | 15 => (orderedInterval (-14798047357 / 1000000000000) (-14798047356 / 1000000000000), orderedInterval (-30640756629 / 1000000000000) (-30640756628 / 1000000000000))
    | 16 => (orderedInterval (23657490087 / 1000000000000) (23657495942 / 1000000000000), orderedInterval (-27441972551 / 1000000000000) (-27441966696 / 1000000000000))
    | 17 => (orderedInterval (16481688144 / 1000000000000) (16481688145 / 1000000000000), orderedInterval (25153173700 / 1000000000000) (25153173701 / 1000000000000))
    | 18 => (orderedInterval (16398831992 / 1000000000000) (16398831993 / 1000000000000), orderedInterval (36949668735 / 1000000000000) (36949668736 / 1000000000000))
    | 19 => (orderedInterval (-32662636802 / 1000000000000) (-32662636801 / 1000000000000), orderedInterval (-29323396616 / 1000000000000) (-29323396615 / 1000000000000))
    | 20 => (orderedInterval (-6169851733 / 1000000000000) (-6169851716 / 1000000000000), orderedInterval (55201970315 / 1000000000000) (55201970331 / 1000000000000))
    | 21 => (orderedInterval (-72631150718 / 1000000000000) (-72631149163 / 1000000000000), orderedInterval (21739337115 / 1000000000000) (21739338671 / 1000000000000))
    | 22 => (orderedInterval (28076511307 / 1000000000000) (28076511308 / 1000000000000), orderedInterval (36332855550 / 1000000000000) (36332855551 / 1000000000000))
    | 23 => (orderedInterval (-29839822835 / 1000000000000) (-29839822834 / 1000000000000), orderedInterval (-25579887046 / 1000000000000) (-25579887045 / 1000000000000))
    | 24 => (orderedInterval (-53719262100 / 1000000000000) (-53719246054 / 1000000000000), orderedInterval (27937307915 / 1000000000000) (27937323961 / 1000000000000))
    | 25 => (orderedInterval (-29718923567 / 1000000000000) (-29718923212 / 1000000000000), orderedInterval (-4052264361 / 1000000000000) (-4052264005 / 1000000000000))
    | _ => (orderedInterval (31139513327 / 1000000000000) (31139615378 / 1000000000000), orderedInterval (-19460701149 / 1000000000000) (-19460599098 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13055885214 / 1000000000000) (-13055885164 / 1000000000000)
      | 1 => orderedInterval (-526481678 / 1000000000000) (-526481631 / 1000000000000)
      | 2 => orderedInterval (842619051 / 1000000000000) (842619187 / 1000000000000)
      | 3 => orderedInterval (657327131 / 1000000000000) (657329613 / 1000000000000)
      | 4 => orderedInterval (-1785545003 / 1000000000000) (-1785544907 / 1000000000000)
      | 5 => orderedInterval (-1102726546 / 1000000000000) (-1102726174 / 1000000000000)
      | 6 => orderedInterval (-974206731 / 1000000000000) (-974206634 / 1000000000000)
      | 7 => orderedInterval (2991065010 / 1000000000000) (2991065084 / 1000000000000)
      | _ => orderedInterval (-3747282110 / 1000000000000) (-3747262731 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-6608019920 / 1000000000000) (-6608019862 / 1000000000000)
      | 1 => orderedInterval (-2570702267 / 1000000000000) (-2570702214 / 1000000000000)
      | 2 => orderedInterval (-2566845937 / 1000000000000) (-2566845734 / 1000000000000)
      | 3 => orderedInterval (14902957785 / 1000000000000) (14902961821 / 1000000000000)
      | 4 => orderedInterval (-3532810180 / 1000000000000) (-3532809998 / 1000000000000)
      | 5 => orderedInterval (2683372225 / 1000000000000) (2683372705 / 1000000000000)
      | 6 => orderedInterval (-3628753167 / 1000000000000) (-3628753078 / 1000000000000)
      | 7 => orderedInterval (1350577445 / 1000000000000) (1350577495 / 1000000000000)
      | _ => orderedInterval (5225345548 / 1000000000000) (5225369576 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11951002306 / 1000000000000) (11951002373 / 1000000000000)
      | 1 => orderedInterval (1713407084 / 1000000000000) (1713407156 / 1000000000000)
      | 2 => orderedInterval (-2318791835 / 1000000000000) (-2318791527 / 1000000000000)
      | 3 => orderedInterval (5771009160 / 1000000000000) (5771016281 / 1000000000000)
      | 4 => orderedInterval (3051050659 / 1000000000000) (3051051012 / 1000000000000)
      | 5 => orderedInterval (1110347938 / 1000000000000) (1110348564 / 1000000000000)
      | 6 => orderedInterval (1421970999 / 1000000000000) (1421971084 / 1000000000000)
      | 7 => orderedInterval (-2394233918 / 1000000000000) (-2394233875 / 1000000000000)
      | _ => orderedInterval (702546020 / 1000000000000) (702575958 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (6561366758 / 1000000000000) (6561366837 / 1000000000000)
      | 1 => orderedInterval (8046866862 / 1000000000000) (8046866971 / 1000000000000)
      | 2 => orderedInterval (8454979316 / 1000000000000) (8454979790 / 1000000000000)
      | 3 => orderedInterval (-79839671934 / 1000000000000) (-79839658388 / 1000000000000)
      | 4 => orderedInterval (8375426151 / 1000000000000) (8375426852 / 1000000000000)
      | 5 => orderedInterval (-6269288464 / 1000000000000) (-6269287645 / 1000000000000)
      | 6 => orderedInterval (4949342254 / 1000000000000) (4949342336 / 1000000000000)
      | 7 => orderedInterval (-2055709794 / 1000000000000) (-2055709751 / 1000000000000)
      | _ => orderedInterval (-9134082178 / 1000000000000) (-9134044883 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10552950129 / 1000000000000) (-10552950035 / 1000000000000)
      | 1 => orderedInterval (-4887134891 / 1000000000000) (-4887134724 / 1000000000000)
      | 2 => orderedInterval (6992529234 / 1000000000000) (6992529974 / 1000000000000)
      | 3 => orderedInterval (-46452569908 / 1000000000000) (-46452542433 / 1000000000000)
      | 4 => orderedInterval (-1973603265 / 1000000000000) (-1973601848 / 1000000000000)
      | 5 => orderedInterval (634483028 / 1000000000000) (634484111 / 1000000000000)
      | 6 => orderedInterval (-1868395436 / 1000000000000) (-1868395355 / 1000000000000)
      | 7 => orderedInterval (2901611410 / 1000000000000) (2901611455 / 1000000000000)
      | _ => orderedInterval (15049463580 / 1000000000000) (15049510227 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-16701116090 / 1000000000000) (-16701093357 / 1000000000000)
    | 1 => orderedInterval (5255121532 / 1000000000000) (5255150711 / 1000000000000)
    | 2 => orderedInterval (21008308413 / 1000000000000) (21008347026 / 1000000000000)
    | 3 => orderedInterval (-60910771029 / 1000000000000) (-60910717881 / 1000000000000)
    | _ => orderedInterval (-40156566377 / 1000000000000) (-40156488628 / 1000000000000)

theorem compactCertificate509_stateChecks0 :
    compactCertificate509.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (761 / 2)) (orderedInterval (-37374722544 / 1000000000000) (-37374722543 / 1000000000000), orderedInterval (-16571443157 / 1000000000000) (-16571443156 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1121098311352661 / 4000000000000)) (orderedInterval (-47355297910 / 1000000000000) (-47355297886 / 1000000000000), orderedInterval (-5290169266 / 1000000000000) (-5290169243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (362540159473013 / 800000000000)) (orderedInterval (37480627434 / 1000000000000) (37480627826 / 1000000000000), orderedInterval (-48221078 / 1000000000000) (-48220686 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks1 :
    compactCertificate509.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (327133691193727 / 4000000000000)) (orderedInterval (68329835068 / 1000000000000) (68329835069 / 1000000000000), orderedInterval (55396422149 / 1000000000000) (55396422150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (878727109706419 / 4000000000000)) (orderedInterval (28372068676 / 1000000000000) (28372068677 / 1000000000000), orderedInterval (45684163007 / 1000000000000) (45684163008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2385915039619623 / 4000000000000)) (orderedInterval (11549715869 / 1000000000000) (11549715870 / 1000000000000), orderedInterval (30550111912 / 1000000000000) (30550111913 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks2 :
    compactCertificate509.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1757454219413599 / 4000000000000)) (orderedInterval (12179686952 / 1000000000000) (12179686953 / 1000000000000), orderedInterval (36050179138 / 1000000000000) (36050179139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3011427759812827 / 4000000000000)) (orderedInterval (-9699343426 / 1000000000000) (-9699343418 / 1000000000000), orderedInterval (27420454904 / 1000000000000) (27420454912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2218204058005393 / 4000000000000)) (orderedInterval (22486424065 / 1000000000000) (22486428752 / 1000000000000), orderedInterval (-25364941620 / 1000000000000) (-25364936933 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks3 :
    compactCertificate509.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (3403295461754239 / 4000000000000)) (orderedInterval (-6435863876 / 1000000000000) (-6435863875 / 1000000000000), orderedInterval (-26582285189 / 1000000000000) (-26582285188 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1964893550975431 / 4000000000000)) (orderedInterval (33826110153 / 1000000000000) (33826131983 / 1000000000000), orderedInterval (-12354397173 / 1000000000000) (-12354375344 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (3486738086793779 / 4000000000000)) (orderedInterval (-21050724406 / 1000000000000) (-21050719386 / 1000000000000), orderedInterval (16959043926 / 1000000000000) (16959048946 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks4 :
    compactCertificate509.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3257763008451551 / 4000000000000)) (orderedInterval (-27954087758 / 1000000000000) (-27954084972 / 1000000000000), orderedInterval (-466404723 / 1000000000000) (-466401938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2324893402573583 / 4000000000000)) (orderedInterval (-24059268672 / 1000000000000) (-24059268671 / 1000000000000), orderedInterval (-22705094647 / 1000000000000) (-22705094646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2636181329119257 / 4000000000000)) (orderedInterval (2981692289 / 1000000000000) (2981692290 / 1000000000000), orderedInterval (30934486949 / 1000000000000) (30934486950 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks5 :
    compactCertificate509.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2197773156500233 / 4000000000000)) (orderedInterval (-14798047357 / 1000000000000) (-14798047356 / 1000000000000), orderedInterval (-30640756629 / 1000000000000) (-30640756628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1941799235540893 / 4000000000000)) (orderedInterval (23657490087 / 1000000000000) (23657495942 / 1000000000000), orderedInterval (-27441972551 / 1000000000000) (-27441966696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (562809103720407 / 800000000000)) (orderedInterval (16481688144 / 1000000000000) (16481688145 / 1000000000000), orderedInterval (25153173700 / 1000000000000) (25153173701 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks6 :
    compactCertificate509.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1556759599911029 / 4000000000000)) (orderedInterval (16398831992 / 1000000000000) (16398831993 / 1000000000000), orderedInterval (36949668735 / 1000000000000) (36949668736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319682353485069 / 4000000000000)) (orderedInterval (-32662636802 / 1000000000000) (-32662636801 / 1000000000000), orderedInterval (-29323396616 / 1000000000000) (-29323396615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (825795941994607 / 4000000000000)) (orderedInterval (-6169851733 / 1000000000000) (-6169851716 / 1000000000000), orderedInterval (55201970315 / 1000000000000) (55201970331 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks7 :
    compactCertificate509.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (444115804077969 / 4000000000000)) (orderedInterval (-72631150718 / 1000000000000) (-72631149163 / 1000000000000), orderedInterval (21739337115 / 1000000000000) (21739338671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1205860800900907 / 4000000000000)) (orderedInterval (28076511307 / 1000000000000) (28076511308 / 1000000000000), orderedInterval (36332855550 / 1000000000000) (36332855551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1646499831419339 / 4000000000000)) (orderedInterval (-29839822835 / 1000000000000) (-29839822834 / 1000000000000), orderedInterval (-25579887046 / 1000000000000) (-25579887045 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_stateChecks8 :
    compactCertificate509.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (696204058005393 / 4000000000000)) (orderedInterval (-53719262100 / 1000000000000) (-53719246054 / 1000000000000), orderedInterval (27937307915 / 1000000000000) (27937323961 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2830030843698353 / 4000000000000)) (orderedInterval (-29718923567 / 1000000000000) (-29718923212 / 1000000000000), orderedInterval (-4052264361 / 1000000000000) (-4052264005 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1890329448460927 / 4000000000000)) (orderedInterval (31139513327 / 1000000000000) (31139615378 / 1000000000000), orderedInterval (-19460701149 / 1000000000000) (-19460599098 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_states : ∀ j,
    BesselStateValid (compactCertificate509.point j) (compactCertificate509.state j) :=
  compactCertificate509.statesValid_of_checks3 compactCertificate509_stateChecks0
    compactCertificate509_stateChecks1 compactCertificate509_stateChecks2
    compactCertificate509_stateChecks3 compactCertificate509_stateChecks4
    compactCertificate509_stateChecks5 compactCertificate509_stateChecks6
    compactCertificate509_stateChecks7 compactCertificate509_stateChecks8

theorem compactCertificate509_chunkChecks0_0 :
    compactCertificate509.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (761 / 2) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37374722544 / 1000000000000) (-37374722543 / 1000000000000), orderedInterval (-16571443157 / 1000000000000) (-16571443156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1121098311352661 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47355297910 / 1000000000000) (-47355297886 / 1000000000000), orderedInterval (-5290169266 / 1000000000000) (-5290169243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (362540159473013 / 800000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37480627434 / 1000000000000) (37480627826 / 1000000000000), orderedInterval (-48221078 / 1000000000000) (-48220686 / 1000000000000)))) (orderedInterval (-13055885214 / 1000000000000) (-13055885164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (327133691193727 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (68329835068 / 1000000000000) (68329835069 / 1000000000000), orderedInterval (55396422149 / 1000000000000) (55396422150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (878727109706419 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28372068676 / 1000000000000) (28372068677 / 1000000000000), orderedInterval (45684163007 / 1000000000000) (45684163008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2385915039619623 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11549715869 / 1000000000000) (11549715870 / 1000000000000), orderedInterval (30550111912 / 1000000000000) (30550111913 / 1000000000000)))) (orderedInterval (-526481678 / 1000000000000) (-526481631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1757454219413599 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12179686952 / 1000000000000) (12179686953 / 1000000000000), orderedInterval (36050179138 / 1000000000000) (36050179139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3011427759812827 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9699343426 / 1000000000000) (-9699343418 / 1000000000000), orderedInterval (27420454904 / 1000000000000) (27420454912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2218204058005393 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22486424065 / 1000000000000) (22486428752 / 1000000000000), orderedInterval (-25364941620 / 1000000000000) (-25364936933 / 1000000000000)))) (orderedInterval (842619051 / 1000000000000) (842619187 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks0_1 :
    compactCertificate509.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3403295461754239 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6435863876 / 1000000000000) (-6435863875 / 1000000000000), orderedInterval (-26582285189 / 1000000000000) (-26582285188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1964893550975431 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33826110153 / 1000000000000) (33826131983 / 1000000000000), orderedInterval (-12354397173 / 1000000000000) (-12354375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3486738086793779 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21050724406 / 1000000000000) (-21050719386 / 1000000000000), orderedInterval (16959043926 / 1000000000000) (16959048946 / 1000000000000)))) (orderedInterval (657327131 / 1000000000000) (657329613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3257763008451551 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27954087758 / 1000000000000) (-27954084972 / 1000000000000), orderedInterval (-466404723 / 1000000000000) (-466401938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2324893402573583 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24059268672 / 1000000000000) (-24059268671 / 1000000000000), orderedInterval (-22705094647 / 1000000000000) (-22705094646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2636181329119257 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2981692289 / 1000000000000) (2981692290 / 1000000000000), orderedInterval (30934486949 / 1000000000000) (30934486950 / 1000000000000)))) (orderedInterval (-1785545003 / 1000000000000) (-1785544907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2197773156500233 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14798047357 / 1000000000000) (-14798047356 / 1000000000000), orderedInterval (-30640756629 / 1000000000000) (-30640756628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1941799235540893 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23657490087 / 1000000000000) (23657495942 / 1000000000000), orderedInterval (-27441972551 / 1000000000000) (-27441966696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (562809103720407 / 800000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16481688144 / 1000000000000) (16481688145 / 1000000000000), orderedInterval (25153173700 / 1000000000000) (25153173701 / 1000000000000)))) (orderedInterval (-1102726546 / 1000000000000) (-1102726174 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks0_2 :
    compactCertificate509.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1556759599911029 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16398831992 / 1000000000000) (16398831993 / 1000000000000), orderedInterval (36949668735 / 1000000000000) (36949668736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1319682353485069 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32662636802 / 1000000000000) (-32662636801 / 1000000000000), orderedInterval (-29323396616 / 1000000000000) (-29323396615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (825795941994607 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-6169851733 / 1000000000000) (-6169851716 / 1000000000000), orderedInterval (55201970315 / 1000000000000) (55201970331 / 1000000000000)))) (orderedInterval (-974206731 / 1000000000000) (-974206634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (444115804077969 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72631150718 / 1000000000000) (-72631149163 / 1000000000000), orderedInterval (21739337115 / 1000000000000) (21739338671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1205860800900907 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28076511307 / 1000000000000) (28076511308 / 1000000000000), orderedInterval (36332855550 / 1000000000000) (36332855551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1646499831419339 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29839822835 / 1000000000000) (-29839822834 / 1000000000000), orderedInterval (-25579887046 / 1000000000000) (-25579887045 / 1000000000000)))) (orderedInterval (2991065010 / 1000000000000) (2991065084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (696204058005393 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53719262100 / 1000000000000) (-53719246054 / 1000000000000), orderedInterval (27937307915 / 1000000000000) (27937323961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2830030843698353 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29718923567 / 1000000000000) (-29718923212 / 1000000000000), orderedInterval (-4052264361 / 1000000000000) (-4052264005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1890329448460927 / 4000000000000) 0 (IntervalRat.scale (761 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31139513327 / 1000000000000) (31139615378 / 1000000000000), orderedInterval (-19460701149 / 1000000000000) (-19460599098 / 1000000000000)))) (orderedInterval (-3747282110 / 1000000000000) (-3747262731 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks0 :
    compactCertificate509.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate509.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate509_chunkChecks0_0
    compactCertificate509_chunkChecks0_1 compactCertificate509_chunkChecks0_2

theorem compactCertificate509_chunkChecks1_0 :
    compactCertificate509.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (761 / 2) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37374722544 / 1000000000000) (-37374722543 / 1000000000000), orderedInterval (-16571443157 / 1000000000000) (-16571443156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1121098311352661 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47355297910 / 1000000000000) (-47355297886 / 1000000000000), orderedInterval (-5290169266 / 1000000000000) (-5290169243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (362540159473013 / 800000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37480627434 / 1000000000000) (37480627826 / 1000000000000), orderedInterval (-48221078 / 1000000000000) (-48220686 / 1000000000000)))) (orderedInterval (-6608019920 / 1000000000000) (-6608019862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (327133691193727 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (68329835068 / 1000000000000) (68329835069 / 1000000000000), orderedInterval (55396422149 / 1000000000000) (55396422150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (878727109706419 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28372068676 / 1000000000000) (28372068677 / 1000000000000), orderedInterval (45684163007 / 1000000000000) (45684163008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2385915039619623 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11549715869 / 1000000000000) (11549715870 / 1000000000000), orderedInterval (30550111912 / 1000000000000) (30550111913 / 1000000000000)))) (orderedInterval (-2570702267 / 1000000000000) (-2570702214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1757454219413599 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12179686952 / 1000000000000) (12179686953 / 1000000000000), orderedInterval (36050179138 / 1000000000000) (36050179139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3011427759812827 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9699343426 / 1000000000000) (-9699343418 / 1000000000000), orderedInterval (27420454904 / 1000000000000) (27420454912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2218204058005393 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22486424065 / 1000000000000) (22486428752 / 1000000000000), orderedInterval (-25364941620 / 1000000000000) (-25364936933 / 1000000000000)))) (orderedInterval (-2566845937 / 1000000000000) (-2566845734 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks1_1 :
    compactCertificate509.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3403295461754239 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6435863876 / 1000000000000) (-6435863875 / 1000000000000), orderedInterval (-26582285189 / 1000000000000) (-26582285188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1964893550975431 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33826110153 / 1000000000000) (33826131983 / 1000000000000), orderedInterval (-12354397173 / 1000000000000) (-12354375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3486738086793779 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21050724406 / 1000000000000) (-21050719386 / 1000000000000), orderedInterval (16959043926 / 1000000000000) (16959048946 / 1000000000000)))) (orderedInterval (14902957785 / 1000000000000) (14902961821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3257763008451551 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27954087758 / 1000000000000) (-27954084972 / 1000000000000), orderedInterval (-466404723 / 1000000000000) (-466401938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2324893402573583 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24059268672 / 1000000000000) (-24059268671 / 1000000000000), orderedInterval (-22705094647 / 1000000000000) (-22705094646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2636181329119257 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2981692289 / 1000000000000) (2981692290 / 1000000000000), orderedInterval (30934486949 / 1000000000000) (30934486950 / 1000000000000)))) (orderedInterval (-3532810180 / 1000000000000) (-3532809998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2197773156500233 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14798047357 / 1000000000000) (-14798047356 / 1000000000000), orderedInterval (-30640756629 / 1000000000000) (-30640756628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1941799235540893 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23657490087 / 1000000000000) (23657495942 / 1000000000000), orderedInterval (-27441972551 / 1000000000000) (-27441966696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (562809103720407 / 800000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16481688144 / 1000000000000) (16481688145 / 1000000000000), orderedInterval (25153173700 / 1000000000000) (25153173701 / 1000000000000)))) (orderedInterval (2683372225 / 1000000000000) (2683372705 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks1_2 :
    compactCertificate509.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1556759599911029 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16398831992 / 1000000000000) (16398831993 / 1000000000000), orderedInterval (36949668735 / 1000000000000) (36949668736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1319682353485069 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32662636802 / 1000000000000) (-32662636801 / 1000000000000), orderedInterval (-29323396616 / 1000000000000) (-29323396615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (825795941994607 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-6169851733 / 1000000000000) (-6169851716 / 1000000000000), orderedInterval (55201970315 / 1000000000000) (55201970331 / 1000000000000)))) (orderedInterval (-3628753167 / 1000000000000) (-3628753078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (444115804077969 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72631150718 / 1000000000000) (-72631149163 / 1000000000000), orderedInterval (21739337115 / 1000000000000) (21739338671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1205860800900907 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28076511307 / 1000000000000) (28076511308 / 1000000000000), orderedInterval (36332855550 / 1000000000000) (36332855551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1646499831419339 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29839822835 / 1000000000000) (-29839822834 / 1000000000000), orderedInterval (-25579887046 / 1000000000000) (-25579887045 / 1000000000000)))) (orderedInterval (1350577445 / 1000000000000) (1350577495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (696204058005393 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53719262100 / 1000000000000) (-53719246054 / 1000000000000), orderedInterval (27937307915 / 1000000000000) (27937323961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2830030843698353 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29718923567 / 1000000000000) (-29718923212 / 1000000000000), orderedInterval (-4052264361 / 1000000000000) (-4052264005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1890329448460927 / 4000000000000) 1 (IntervalRat.scale (761 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31139513327 / 1000000000000) (31139615378 / 1000000000000), orderedInterval (-19460701149 / 1000000000000) (-19460599098 / 1000000000000)))) (orderedInterval (5225345548 / 1000000000000) (5225369576 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks1 :
    compactCertificate509.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate509.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate509_chunkChecks1_0
    compactCertificate509_chunkChecks1_1 compactCertificate509_chunkChecks1_2

theorem compactCertificate509_chunkChecks2_0 :
    compactCertificate509.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (761 / 2) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37374722544 / 1000000000000) (-37374722543 / 1000000000000), orderedInterval (-16571443157 / 1000000000000) (-16571443156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1121098311352661 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47355297910 / 1000000000000) (-47355297886 / 1000000000000), orderedInterval (-5290169266 / 1000000000000) (-5290169243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (362540159473013 / 800000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37480627434 / 1000000000000) (37480627826 / 1000000000000), orderedInterval (-48221078 / 1000000000000) (-48220686 / 1000000000000)))) (orderedInterval (11951002306 / 1000000000000) (11951002373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (327133691193727 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (68329835068 / 1000000000000) (68329835069 / 1000000000000), orderedInterval (55396422149 / 1000000000000) (55396422150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (878727109706419 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28372068676 / 1000000000000) (28372068677 / 1000000000000), orderedInterval (45684163007 / 1000000000000) (45684163008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2385915039619623 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11549715869 / 1000000000000) (11549715870 / 1000000000000), orderedInterval (30550111912 / 1000000000000) (30550111913 / 1000000000000)))) (orderedInterval (1713407084 / 1000000000000) (1713407156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1757454219413599 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12179686952 / 1000000000000) (12179686953 / 1000000000000), orderedInterval (36050179138 / 1000000000000) (36050179139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3011427759812827 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9699343426 / 1000000000000) (-9699343418 / 1000000000000), orderedInterval (27420454904 / 1000000000000) (27420454912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2218204058005393 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22486424065 / 1000000000000) (22486428752 / 1000000000000), orderedInterval (-25364941620 / 1000000000000) (-25364936933 / 1000000000000)))) (orderedInterval (-2318791835 / 1000000000000) (-2318791527 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks2_1 :
    compactCertificate509.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3403295461754239 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6435863876 / 1000000000000) (-6435863875 / 1000000000000), orderedInterval (-26582285189 / 1000000000000) (-26582285188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1964893550975431 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33826110153 / 1000000000000) (33826131983 / 1000000000000), orderedInterval (-12354397173 / 1000000000000) (-12354375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3486738086793779 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21050724406 / 1000000000000) (-21050719386 / 1000000000000), orderedInterval (16959043926 / 1000000000000) (16959048946 / 1000000000000)))) (orderedInterval (5771009160 / 1000000000000) (5771016281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3257763008451551 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27954087758 / 1000000000000) (-27954084972 / 1000000000000), orderedInterval (-466404723 / 1000000000000) (-466401938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2324893402573583 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24059268672 / 1000000000000) (-24059268671 / 1000000000000), orderedInterval (-22705094647 / 1000000000000) (-22705094646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2636181329119257 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2981692289 / 1000000000000) (2981692290 / 1000000000000), orderedInterval (30934486949 / 1000000000000) (30934486950 / 1000000000000)))) (orderedInterval (3051050659 / 1000000000000) (3051051012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2197773156500233 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14798047357 / 1000000000000) (-14798047356 / 1000000000000), orderedInterval (-30640756629 / 1000000000000) (-30640756628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1941799235540893 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23657490087 / 1000000000000) (23657495942 / 1000000000000), orderedInterval (-27441972551 / 1000000000000) (-27441966696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (562809103720407 / 800000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16481688144 / 1000000000000) (16481688145 / 1000000000000), orderedInterval (25153173700 / 1000000000000) (25153173701 / 1000000000000)))) (orderedInterval (1110347938 / 1000000000000) (1110348564 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks2_2 :
    compactCertificate509.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1556759599911029 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16398831992 / 1000000000000) (16398831993 / 1000000000000), orderedInterval (36949668735 / 1000000000000) (36949668736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1319682353485069 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32662636802 / 1000000000000) (-32662636801 / 1000000000000), orderedInterval (-29323396616 / 1000000000000) (-29323396615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (825795941994607 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-6169851733 / 1000000000000) (-6169851716 / 1000000000000), orderedInterval (55201970315 / 1000000000000) (55201970331 / 1000000000000)))) (orderedInterval (1421970999 / 1000000000000) (1421971084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (444115804077969 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72631150718 / 1000000000000) (-72631149163 / 1000000000000), orderedInterval (21739337115 / 1000000000000) (21739338671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1205860800900907 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28076511307 / 1000000000000) (28076511308 / 1000000000000), orderedInterval (36332855550 / 1000000000000) (36332855551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1646499831419339 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29839822835 / 1000000000000) (-29839822834 / 1000000000000), orderedInterval (-25579887046 / 1000000000000) (-25579887045 / 1000000000000)))) (orderedInterval (-2394233918 / 1000000000000) (-2394233875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (696204058005393 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53719262100 / 1000000000000) (-53719246054 / 1000000000000), orderedInterval (27937307915 / 1000000000000) (27937323961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2830030843698353 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29718923567 / 1000000000000) (-29718923212 / 1000000000000), orderedInterval (-4052264361 / 1000000000000) (-4052264005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1890329448460927 / 4000000000000) 2 (IntervalRat.scale (761 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31139513327 / 1000000000000) (31139615378 / 1000000000000), orderedInterval (-19460701149 / 1000000000000) (-19460599098 / 1000000000000)))) (orderedInterval (702546020 / 1000000000000) (702575958 / 1000000000000))) = true
  rfl'

theorem compactCertificate509_chunkChecks2 :
    compactCertificate509.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate509.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate509_chunkChecks2_0
    compactCertificate509_chunkChecks2_1 compactCertificate509_chunkChecks2_2

theorem compactCertificate509_chunkChecks3_0 :
    compactCertificate509.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (761 / 2) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37374722544 / 1000000000000) (-37374722543 / 1000000000000), orderedInterval (-16571443157 / 1000000000000) (-16571443156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1121098311352661 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47355297910 / 1000000000000) (-47355297886 / 1000000000000), orderedInterval (-5290169266 / 1000000000000) (-5290169243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (362540159473013 / 800000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37480627434 / 1000000000000) (37480627826 / 1000000000000), orderedInterval (-48221078 / 1000000000000) (-48220686 / 1000000000000)))) (orderedInterval (6561366758 / 1000000000000) (6561366837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (327133691193727 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (68329835068 / 1000000000000) (68329835069 / 1000000000000), orderedInterval (55396422149 / 1000000000000) (55396422150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (878727109706419 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28372068676 / 1000000000000) (28372068677 / 1000000000000), orderedInterval (45684163007 / 1000000000000) (45684163008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2385915039619623 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11549715869 / 1000000000000) (11549715870 / 1000000000000), orderedInterval (30550111912 / 1000000000000) (30550111913 / 1000000000000)))) (orderedInterval (8046866862 / 1000000000000) (8046866971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1757454219413599 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12179686952 / 1000000000000) (12179686953 / 1000000000000), orderedInterval (36050179138 / 1000000000000) (36050179139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3011427759812827 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9699343426 / 1000000000000) (-9699343418 / 1000000000000), orderedInterval (27420454904 / 1000000000000) (27420454912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2218204058005393 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22486424065 / 1000000000000) (22486428752 / 1000000000000), orderedInterval (-25364941620 / 1000000000000) (-25364936933 / 1000000000000)))) (orderedInterval (8454979316 / 1000000000000) (8454979790 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate509_chunkChecks3_1 :
    compactCertificate509.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3403295461754239 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6435863876 / 1000000000000) (-6435863875 / 1000000000000), orderedInterval (-26582285189 / 1000000000000) (-26582285188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1964893550975431 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33826110153 / 1000000000000) (33826131983 / 1000000000000), orderedInterval (-12354397173 / 1000000000000) (-12354375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3486738086793779 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21050724406 / 1000000000000) (-21050719386 / 1000000000000), orderedInterval (16959043926 / 1000000000000) (16959048946 / 1000000000000)))) (orderedInterval (-79839671934 / 1000000000000) (-79839658388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3257763008451551 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27954087758 / 1000000000000) (-27954084972 / 1000000000000), orderedInterval (-466404723 / 1000000000000) (-466401938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2324893402573583 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24059268672 / 1000000000000) (-24059268671 / 1000000000000), orderedInterval (-22705094647 / 1000000000000) (-22705094646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2636181329119257 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2981692289 / 1000000000000) (2981692290 / 1000000000000), orderedInterval (30934486949 / 1000000000000) (30934486950 / 1000000000000)))) (orderedInterval (8375426151 / 1000000000000) (8375426852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2197773156500233 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14798047357 / 1000000000000) (-14798047356 / 1000000000000), orderedInterval (-30640756629 / 1000000000000) (-30640756628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1941799235540893 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23657490087 / 1000000000000) (23657495942 / 1000000000000), orderedInterval (-27441972551 / 1000000000000) (-27441966696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (562809103720407 / 800000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16481688144 / 1000000000000) (16481688145 / 1000000000000), orderedInterval (25153173700 / 1000000000000) (25153173701 / 1000000000000)))) (orderedInterval (-6269288464 / 1000000000000) (-6269287645 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate509_chunkChecks3_2 :
    compactCertificate509.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1556759599911029 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16398831992 / 1000000000000) (16398831993 / 1000000000000), orderedInterval (36949668735 / 1000000000000) (36949668736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1319682353485069 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32662636802 / 1000000000000) (-32662636801 / 1000000000000), orderedInterval (-29323396616 / 1000000000000) (-29323396615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (825795941994607 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-6169851733 / 1000000000000) (-6169851716 / 1000000000000), orderedInterval (55201970315 / 1000000000000) (55201970331 / 1000000000000)))) (orderedInterval (4949342254 / 1000000000000) (4949342336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (444115804077969 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72631150718 / 1000000000000) (-72631149163 / 1000000000000), orderedInterval (21739337115 / 1000000000000) (21739338671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1205860800900907 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28076511307 / 1000000000000) (28076511308 / 1000000000000), orderedInterval (36332855550 / 1000000000000) (36332855551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1646499831419339 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29839822835 / 1000000000000) (-29839822834 / 1000000000000), orderedInterval (-25579887046 / 1000000000000) (-25579887045 / 1000000000000)))) (orderedInterval (-2055709794 / 1000000000000) (-2055709751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (696204058005393 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53719262100 / 1000000000000) (-53719246054 / 1000000000000), orderedInterval (27937307915 / 1000000000000) (27937323961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2830030843698353 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29718923567 / 1000000000000) (-29718923212 / 1000000000000), orderedInterval (-4052264361 / 1000000000000) (-4052264005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1890329448460927 / 4000000000000) 3 (IntervalRat.scale (761 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31139513327 / 1000000000000) (31139615378 / 1000000000000), orderedInterval (-19460701149 / 1000000000000) (-19460599098 / 1000000000000)))) (orderedInterval (-9134082178 / 1000000000000) (-9134044883 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate509_chunkChecks3 :
    compactCertificate509.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate509.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate509_chunkChecks3_0
    compactCertificate509_chunkChecks3_1 compactCertificate509_chunkChecks3_2

theorem compactCertificate509_chunkChecks4_0 :
    compactCertificate509.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (761 / 2) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-37374722544 / 1000000000000) (-37374722543 / 1000000000000), orderedInterval (-16571443157 / 1000000000000) (-16571443156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1121098311352661 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47355297910 / 1000000000000) (-47355297886 / 1000000000000), orderedInterval (-5290169266 / 1000000000000) (-5290169243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (362540159473013 / 800000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37480627434 / 1000000000000) (37480627826 / 1000000000000), orderedInterval (-48221078 / 1000000000000) (-48220686 / 1000000000000)))) (orderedInterval (-10552950129 / 1000000000000) (-10552950035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (327133691193727 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (68329835068 / 1000000000000) (68329835069 / 1000000000000), orderedInterval (55396422149 / 1000000000000) (55396422150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (878727109706419 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28372068676 / 1000000000000) (28372068677 / 1000000000000), orderedInterval (45684163007 / 1000000000000) (45684163008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2385915039619623 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (11549715869 / 1000000000000) (11549715870 / 1000000000000), orderedInterval (30550111912 / 1000000000000) (30550111913 / 1000000000000)))) (orderedInterval (-4887134891 / 1000000000000) (-4887134724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1757454219413599 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12179686952 / 1000000000000) (12179686953 / 1000000000000), orderedInterval (36050179138 / 1000000000000) (36050179139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3011427759812827 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9699343426 / 1000000000000) (-9699343418 / 1000000000000), orderedInterval (27420454904 / 1000000000000) (27420454912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2218204058005393 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22486424065 / 1000000000000) (22486428752 / 1000000000000), orderedInterval (-25364941620 / 1000000000000) (-25364936933 / 1000000000000)))) (orderedInterval (6992529234 / 1000000000000) (6992529974 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate509_chunkChecks4_1 :
    compactCertificate509.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3403295461754239 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6435863876 / 1000000000000) (-6435863875 / 1000000000000), orderedInterval (-26582285189 / 1000000000000) (-26582285188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1964893550975431 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33826110153 / 1000000000000) (33826131983 / 1000000000000), orderedInterval (-12354397173 / 1000000000000) (-12354375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3486738086793779 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21050724406 / 1000000000000) (-21050719386 / 1000000000000), orderedInterval (16959043926 / 1000000000000) (16959048946 / 1000000000000)))) (orderedInterval (-46452569908 / 1000000000000) (-46452542433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3257763008451551 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27954087758 / 1000000000000) (-27954084972 / 1000000000000), orderedInterval (-466404723 / 1000000000000) (-466401938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2324893402573583 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24059268672 / 1000000000000) (-24059268671 / 1000000000000), orderedInterval (-22705094647 / 1000000000000) (-22705094646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2636181329119257 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2981692289 / 1000000000000) (2981692290 / 1000000000000), orderedInterval (30934486949 / 1000000000000) (30934486950 / 1000000000000)))) (orderedInterval (-1973603265 / 1000000000000) (-1973601848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2197773156500233 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14798047357 / 1000000000000) (-14798047356 / 1000000000000), orderedInterval (-30640756629 / 1000000000000) (-30640756628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1941799235540893 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23657490087 / 1000000000000) (23657495942 / 1000000000000), orderedInterval (-27441972551 / 1000000000000) (-27441966696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (562809103720407 / 800000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16481688144 / 1000000000000) (16481688145 / 1000000000000), orderedInterval (25153173700 / 1000000000000) (25153173701 / 1000000000000)))) (orderedInterval (634483028 / 1000000000000) (634484111 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate509_chunkChecks4_2 :
    compactCertificate509.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1556759599911029 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16398831992 / 1000000000000) (16398831993 / 1000000000000), orderedInterval (36949668735 / 1000000000000) (36949668736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1319682353485069 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32662636802 / 1000000000000) (-32662636801 / 1000000000000), orderedInterval (-29323396616 / 1000000000000) (-29323396615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (825795941994607 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-6169851733 / 1000000000000) (-6169851716 / 1000000000000), orderedInterval (55201970315 / 1000000000000) (55201970331 / 1000000000000)))) (orderedInterval (-1868395436 / 1000000000000) (-1868395355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (444115804077969 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72631150718 / 1000000000000) (-72631149163 / 1000000000000), orderedInterval (21739337115 / 1000000000000) (21739338671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1205860800900907 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28076511307 / 1000000000000) (28076511308 / 1000000000000), orderedInterval (36332855550 / 1000000000000) (36332855551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1646499831419339 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29839822835 / 1000000000000) (-29839822834 / 1000000000000), orderedInterval (-25579887046 / 1000000000000) (-25579887045 / 1000000000000)))) (orderedInterval (2901611410 / 1000000000000) (2901611455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (696204058005393 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53719262100 / 1000000000000) (-53719246054 / 1000000000000), orderedInterval (27937307915 / 1000000000000) (27937323961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2830030843698353 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29718923567 / 1000000000000) (-29718923212 / 1000000000000), orderedInterval (-4052264361 / 1000000000000) (-4052264005 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1890329448460927 / 4000000000000) 4 (IntervalRat.scale (761 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31139513327 / 1000000000000) (31139615378 / 1000000000000), orderedInterval (-19460701149 / 1000000000000) (-19460599098 / 1000000000000)))) (orderedInterval (15049463580 / 1000000000000) (15049510227 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate509_chunkChecks4 :
    compactCertificate509.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate509.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate509_chunkChecks4_0
    compactCertificate509_chunkChecks4_1 compactCertificate509_chunkChecks4_2

theorem compactCertificate509_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate509.chunkCheck r b = true :=
  compactCertificate509.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate509_chunkChecks0
    · exact compactCertificate509_chunkChecks1
    · exact compactCertificate509_chunkChecks2
    · exact compactCertificate509_chunkChecks3
    · exact compactCertificate509_chunkChecks4)

theorem compactCertificate509_coefficient0 :
    compactCertificate509.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate509_coefficient1 :
    compactCertificate509.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate509_coefficient2 :
    compactCertificate509.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate509_coefficient3 :
    compactCertificate509.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate509_coefficient4 :
    compactCertificate509.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate509_coefficients : ∀ r : Fin 5,
    compactCertificate509.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate509_coefficient0
  · exact compactCertificate509_coefficient1
  · exact compactCertificate509_coefficient2
  · exact compactCertificate509_coefficient3
  · exact compactCertificate509_coefficient4

theorem compactCertificate509_lower : (1 : ℚ) ≤ compactCertificate509.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate509, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate509_proves {t : ℝ} (ht : t ∈ compactCertificate509.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate509.proves compactCertificate509_states compactCertificate509_chunks
    compactCertificate509_coefficients compactCertificate509_lower ht

end Erdos232
