/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate455 : CompactCertificate where
  left := 326
  right := 327
  center := 653 / 2
  grid := fun i =>
    match i.val with
    | 0 => 104
    | 1 => 77
    | 2 => 124
    | 3 => 22
    | 4 => 60
    | 5 => 163
    | 6 => 120
    | 7 => 206
    | 8 => 152
    | 9 => 233
    | 10 => 134
    | 11 => 238
    | 12 => 223
    | 13 => 159
    | 14 => 180
    | 15 => 150
    | 16 => 133
    | 17 => 192
    | 18 => 106
    | 19 => 90
    | 20 => 56
    | 21 => 30
    | 22 => 82
    | 23 => 112
    | 24 => 48
    | 25 => 193
    | _ => 129
  point := fun i =>
    match i.val with
    | 0 => 653 / 2
    | 1 => 961993688979353 / 4000000000000
    | 2 => 311088993608249 / 800000000000
    | 3 => 280707359197771 / 4000000000000
    | 4 => 754019451561487 / 4000000000000
    | 5 => 2047309488661779 / 4000000000000
    | 6 => 1508038903123627 / 4000000000000
    | 7 => 2584050364202071 / 4000000000000
    | 8 => 1903399802729989 / 4000000000000
    | 9 => 2920304778614347 / 4000000000000
    | 10 => 1686038750048563 / 4000000000000
    | 11 => 2991905349114767 / 4000000000000
    | 12 => 2795426076897323 / 4000000000000
    | 13 => 1994947952536859 / 4000000000000
    | 14 => 2262058354684461 / 4000000000000
    | 15 => 1885868424697309 / 4000000000000
    | 16 => 1666221945871489 / 4000000000000
    | 17 => 482936064033411 / 800000000000
    | 18 => 1335826568649017 / 4000000000000
    | 19 => 1132394976117937 / 4000000000000
    | 20 => 708600197270011 / 4000000000000
    | 21 => 381087542789637 / 4000000000000
    | 22 => 1034726810759911 / 4000000000000
    | 23 => 1412830998576647 / 4000000000000
    | 24 => 597399802729989 / 4000000000000
    | 25 => 2428397031452069 / 4000000000000
    | _ => 1622056675223371 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (23432291653 / 1000000000000) (23432291654 / 1000000000000), orderedInterval (37390838509 / 1000000000000) (37390838510 / 1000000000000))
    | 1 => (orderedInterval (29866215276 / 1000000000000) (29866223357 / 1000000000000), orderedInterval (-41955959807 / 1000000000000) (-41955951726 / 1000000000000))
    | 2 => (orderedInterval (3589461855 / 1000000000000) (3589461856 / 1000000000000), orderedInterval (40297441116 / 1000000000000) (40297441117 / 1000000000000))
    | 3 => (orderedInterval (91674993336 / 1000000000000) (91674994405 / 1000000000000), orderedInterval (-26482381639 / 1000000000000) (-26482380570 / 1000000000000))
    | 4 => (orderedInterval (41446067917 / 1000000000000) (41446067918 / 1000000000000), orderedInterval (40626160992 / 1000000000000) (40626160993 / 1000000000000))
    | 5 => (orderedInterval (-17917927873 / 1000000000000) (-17917927872 / 1000000000000), orderedInterval (-30359551804 / 1000000000000) (-30359551803 / 1000000000000))
    | 6 => (orderedInterval (29583009422 / 1000000000000) (29583009423 / 1000000000000), orderedInterval (28481785727 / 1000000000000) (28481785728 / 1000000000000))
    | 7 => (orderedInterval (-11360359297 / 1000000000000) (-11360359269 / 1000000000000), orderedInterval (29273152742 / 1000000000000) (29273152770 / 1000000000000))
    | 8 => (orderedInterval (-28353504769 / 1000000000000) (-28353471170 / 1000000000000), orderedInterval (23136868844 / 1000000000000) (23136902443 / 1000000000000))
    | 9 => (orderedInterval (26702581224 / 1000000000000) (26702672102 / 1000000000000), orderedInterval (-12626282314 / 1000000000000) (-12626191436 / 1000000000000))
    | 10 => (orderedInterval (37660370183 / 1000000000000) (37660370191 / 1000000000000), orderedInterval (9548452833 / 1000000000000) (9548452842 / 1000000000000))
    | 11 => (orderedInterval (25485919426 / 1000000000000) (25485919428 / 1000000000000), orderedInterval (14181226988 / 1000000000000) (14181226991 / 1000000000000))
    | 12 => (orderedInterval (24255997194 / 1000000000000) (24256015275 / 1000000000000), orderedInterval (-17978180564 / 1000000000000) (-17978162484 / 1000000000000))
    | 13 => (orderedInterval (-318105445 / 1000000000000) (-318105444 / 1000000000000), orderedInterval (-35725909175 / 1000000000000) (-35725909174 / 1000000000000))
    | 14 => (orderedInterval (24372589481 / 1000000000000) (24372589482 / 1000000000000), orderedInterval (23037336977 / 1000000000000) (23037336978 / 1000000000000))
    | 15 => (orderedInterval (31183107552 / 1000000000000) (31183107553 / 1000000000000), orderedInterval (19406803029 / 1000000000000) (19406803030 / 1000000000000))
    | 16 => (orderedInterval (18441068744 / 1000000000000) (18441069469 / 1000000000000), orderedInterval (-34492743764 / 1000000000000) (-34492743040 / 1000000000000))
    | 17 => (orderedInterval (31011266140 / 1000000000000) (31011266156 / 1000000000000), orderedInterval (9611915701 / 1000000000000) (9611915717 / 1000000000000))
    | 18 => (orderedInterval (43089099329 / 1000000000000) (43089100678 / 1000000000000), orderedInterval (-7108810499 / 1000000000000) (-7108809150 / 1000000000000))
    | 19 => (orderedInterval (43095475755 / 1000000000000) (43095475756 / 1000000000000), orderedInterval (19711076227 / 1000000000000) (19711076228 / 1000000000000))
    | 20 => (orderedInterval (54370409450 / 1000000000000) (54370420203 / 1000000000000), orderedInterval (-25402702591 / 1000000000000) (-25402691838 / 1000000000000))
    | 21 => (orderedInterval (79451161581 / 1000000000000) (79451162374 / 1000000000000), orderedInterval (-19641106275 / 1000000000000) (-19641105482 / 1000000000000))
    | 22 => (orderedInterval (47604328996 / 1000000000000) (47604332497 / 1000000000000), orderedInterval (-14050513042 / 1000000000000) (-14050509541 / 1000000000000))
    | 23 => (orderedInterval (35887954323 / 1000000000000) (35888033652 / 1000000000000), orderedInterval (-22732237137 / 1000000000000) (-22732157808 / 1000000000000))
    | 24 => (orderedInterval (-40129204224 / 1000000000000) (-40129184978 / 1000000000000), orderedInterval (51634412772 / 1000000000000) (51634432018 / 1000000000000))
    | 25 => (orderedInterval (-32379431252 / 1000000000000) (-32379430386 / 1000000000000), orderedInterval (-417877046 / 1000000000000) (-417876179 / 1000000000000))
    | _ => (orderedInterval (-34045336059 / 1000000000000) (-34045336058 / 1000000000000), orderedInterval (-20226769354 / 1000000000000) (-20226769353 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9776669005 / 1000000000000) (9776669104 / 1000000000000)
      | 1 => orderedInterval (1792438653 / 1000000000000) (1792438704 / 1000000000000)
      | 2 => orderedInterval (-334849346 / 1000000000000) (-334848514 / 1000000000000)
      | 3 => orderedInterval (1668554644 / 1000000000000) (1668570922 / 1000000000000)
      | 4 => orderedInterval (-591316253 / 1000000000000) (-591315888 / 1000000000000)
      | 5 => orderedInterval (98782001 / 1000000000000) (98782075 / 1000000000000)
      | 6 => orderedInterval (-7558780190 / 1000000000000) (-7558779542 / 1000000000000)
      | 7 => orderedInterval (-5297486296 / 1000000000000) (-5297480083 / 1000000000000)
      | _ => orderedInterval (8781639286 / 1000000000000) (8781639563 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (17348804366 / 1000000000000) (17348804448 / 1000000000000)
      | 1 => orderedInterval (4301468315 / 1000000000000) (4301468362 / 1000000000000)
      | 2 => orderedInterval (-971526267 / 1000000000000) (-971525049 / 1000000000000)
      | 3 => orderedInterval (10548309105 / 1000000000000) (10548345483 / 1000000000000)
      | 4 => orderedInterval (-4667725710 / 1000000000000) (-4667724948 / 1000000000000)
      | 5 => orderedInterval (3296978136 / 1000000000000) (3296978236 / 1000000000000)
      | 6 => orderedInterval (-253444282 / 1000000000000) (-253443796 / 1000000000000)
      | 7 => orderedInterval (2243055100 / 1000000000000) (2243061779 / 1000000000000)
      | _ => orderedInterval (4919133595 / 1000000000000) (4919133907 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9790650817 / 1000000000000) (-9790650745 / 1000000000000)
      | 1 => orderedInterval (-3601867745 / 1000000000000) (-3601867682 / 1000000000000)
      | 2 => orderedInterval (86744661 / 1000000000000) (86746450 / 1000000000000)
      | 3 => orderedInterval (26739564 / 1000000000000) (26820991 / 1000000000000)
      | 4 => orderedInterval (2460730983 / 1000000000000) (2460732586 / 1000000000000)
      | 5 => orderedInterval (-1757486653 / 1000000000000) (-1757486516 / 1000000000000)
      | 6 => orderedInterval (8521430350 / 1000000000000) (8521430753 / 1000000000000)
      | 7 => orderedInterval (4014761177 / 1000000000000) (4014768399 / 1000000000000)
      | _ => orderedInterval (-18930998668 / 1000000000000) (-18930998211 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-18628966577 / 1000000000000) (-18628966512 / 1000000000000)
      | 1 => orderedInterval (-8591489923 / 1000000000000) (-8591489830 / 1000000000000)
      | 2 => orderedInterval (5262492069 / 1000000000000) (5262494698 / 1000000000000)
      | 3 => orderedInterval (-50843487535 / 1000000000000) (-50843305483 / 1000000000000)
      | 4 => orderedInterval (9456562351 / 1000000000000) (9456565734 / 1000000000000)
      | 5 => orderedInterval (-6324002755 / 1000000000000) (-6324002562 / 1000000000000)
      | 6 => orderedInterval (-383062055 / 1000000000000) (-383061697 / 1000000000000)
      | 7 => orderedInterval (-2385445743 / 1000000000000) (-2385437948 / 1000000000000)
      | _ => orderedInterval (-7461364965 / 1000000000000) (-7461364209 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9907499414 / 1000000000000) (9907499477 / 1000000000000)
      | 1 => orderedInterval (7910897513 / 1000000000000) (7910897656 / 1000000000000)
      | 2 => orderedInterval (2246322683 / 1000000000000) (2246326567 / 1000000000000)
      | 3 => orderedInterval (-10766944783 / 1000000000000) (-10766537174 / 1000000000000)
      | 4 => orderedInterval (-10523313679 / 1000000000000) (-10523306500 / 1000000000000)
      | 5 => orderedInterval (8087113773 / 1000000000000) (8087114053 / 1000000000000)
      | 6 => orderedInterval (-8763763631 / 1000000000000) (-8763763293 / 1000000000000)
      | 7 => orderedInterval (-4188461098 / 1000000000000) (-4188452655 / 1000000000000)
      | _ => orderedInterval (46742076893 / 1000000000000) (46742078208 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (8335651504 / 1000000000000) (8335676341 / 1000000000000)
    | 1 => orderedInterval (36765052358 / 1000000000000) (36765098422 / 1000000000000)
    | 2 => orderedInterval (-18970597148 / 1000000000000) (-18970503975 / 1000000000000)
    | 3 => orderedInterval (-79898765133 / 1000000000000) (-79898567809 / 1000000000000)
    | _ => orderedInterval (40651427085 / 1000000000000) (40651856339 / 1000000000000)

theorem compactCertificate455_stateChecks0 :
    compactCertificate455.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (653 / 2)) (orderedInterval (23432291653 / 1000000000000) (23432291654 / 1000000000000), orderedInterval (37390838509 / 1000000000000) (37390838510 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (961993688979353 / 4000000000000)) (orderedInterval (29866215276 / 1000000000000) (29866223357 / 1000000000000), orderedInterval (-41955959807 / 1000000000000) (-41955951726 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (311088993608249 / 800000000000)) (orderedInterval (3589461855 / 1000000000000) (3589461856 / 1000000000000), orderedInterval (40297441116 / 1000000000000) (40297441117 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks1 :
    compactCertificate455.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (280707359197771 / 4000000000000)) (orderedInterval (91674993336 / 1000000000000) (91674994405 / 1000000000000), orderedInterval (-26482381639 / 1000000000000) (-26482380570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (754019451561487 / 4000000000000)) (orderedInterval (41446067917 / 1000000000000) (41446067918 / 1000000000000), orderedInterval (40626160992 / 1000000000000) (40626160993 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2047309488661779 / 4000000000000)) (orderedInterval (-17917927873 / 1000000000000) (-17917927872 / 1000000000000), orderedInterval (-30359551804 / 1000000000000) (-30359551803 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks2 :
    compactCertificate455.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1508038903123627 / 4000000000000)) (orderedInterval (29583009422 / 1000000000000) (29583009423 / 1000000000000), orderedInterval (28481785727 / 1000000000000) (28481785728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2584050364202071 / 4000000000000)) (orderedInterval (-11360359297 / 1000000000000) (-11360359269 / 1000000000000), orderedInterval (29273152742 / 1000000000000) (29273152770 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1903399802729989 / 4000000000000)) (orderedInterval (-28353504769 / 1000000000000) (-28353471170 / 1000000000000), orderedInterval (23136868844 / 1000000000000) (23136902443 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks3 :
    compactCertificate455.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2920304778614347 / 4000000000000)) (orderedInterval (26702581224 / 1000000000000) (26702672102 / 1000000000000), orderedInterval (-12626282314 / 1000000000000) (-12626191436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1686038750048563 / 4000000000000)) (orderedInterval (37660370183 / 1000000000000) (37660370191 / 1000000000000), orderedInterval (9548452833 / 1000000000000) (9548452842 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2991905349114767 / 4000000000000)) (orderedInterval (25485919426 / 1000000000000) (25485919428 / 1000000000000), orderedInterval (14181226988 / 1000000000000) (14181226991 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks4 :
    compactCertificate455.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2795426076897323 / 4000000000000)) (orderedInterval (24255997194 / 1000000000000) (24256015275 / 1000000000000), orderedInterval (-17978180564 / 1000000000000) (-17978162484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1994947952536859 / 4000000000000)) (orderedInterval (-318105445 / 1000000000000) (-318105444 / 1000000000000), orderedInterval (-35725909175 / 1000000000000) (-35725909174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2262058354684461 / 4000000000000)) (orderedInterval (24372589481 / 1000000000000) (24372589482 / 1000000000000), orderedInterval (23037336977 / 1000000000000) (23037336978 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks5 :
    compactCertificate455.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1885868424697309 / 4000000000000)) (orderedInterval (31183107552 / 1000000000000) (31183107553 / 1000000000000), orderedInterval (19406803029 / 1000000000000) (19406803030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1666221945871489 / 4000000000000)) (orderedInterval (18441068744 / 1000000000000) (18441069469 / 1000000000000), orderedInterval (-34492743764 / 1000000000000) (-34492743040 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (482936064033411 / 800000000000)) (orderedInterval (31011266140 / 1000000000000) (31011266156 / 1000000000000), orderedInterval (9611915701 / 1000000000000) (9611915717 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks6 :
    compactCertificate455.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1335826568649017 / 4000000000000)) (orderedInterval (43089099329 / 1000000000000) (43089100678 / 1000000000000), orderedInterval (-7108810499 / 1000000000000) (-7108809150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1132394976117937 / 4000000000000)) (orderedInterval (43095475755 / 1000000000000) (43095475756 / 1000000000000), orderedInterval (19711076227 / 1000000000000) (19711076228 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (708600197270011 / 4000000000000)) (orderedInterval (54370409450 / 1000000000000) (54370420203 / 1000000000000), orderedInterval (-25402702591 / 1000000000000) (-25402691838 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks7 :
    compactCertificate455.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (381087542789637 / 4000000000000)) (orderedInterval (79451161581 / 1000000000000) (79451162374 / 1000000000000), orderedInterval (-19641106275 / 1000000000000) (-19641105482 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1034726810759911 / 4000000000000)) (orderedInterval (47604328996 / 1000000000000) (47604332497 / 1000000000000), orderedInterval (-14050513042 / 1000000000000) (-14050509541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1412830998576647 / 4000000000000)) (orderedInterval (35887954323 / 1000000000000) (35888033652 / 1000000000000), orderedInterval (-22732237137 / 1000000000000) (-22732157808 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_stateChecks8 :
    compactCertificate455.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (597399802729989 / 4000000000000)) (orderedInterval (-40129204224 / 1000000000000) (-40129184978 / 1000000000000), orderedInterval (51634412772 / 1000000000000) (51634432018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2428397031452069 / 4000000000000)) (orderedInterval (-32379431252 / 1000000000000) (-32379430386 / 1000000000000), orderedInterval (-417877046 / 1000000000000) (-417876179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1622056675223371 / 4000000000000)) (orderedInterval (-34045336059 / 1000000000000) (-34045336058 / 1000000000000), orderedInterval (-20226769354 / 1000000000000) (-20226769353 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_states : ∀ j,
    BesselStateValid (compactCertificate455.point j) (compactCertificate455.state j) :=
  compactCertificate455.statesValid_of_checks3 compactCertificate455_stateChecks0
    compactCertificate455_stateChecks1 compactCertificate455_stateChecks2
    compactCertificate455_stateChecks3 compactCertificate455_stateChecks4
    compactCertificate455_stateChecks5 compactCertificate455_stateChecks6
    compactCertificate455_stateChecks7 compactCertificate455_stateChecks8

theorem compactCertificate455_chunkChecks0_0 :
    compactCertificate455.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (653 / 2) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23432291653 / 1000000000000) (23432291654 / 1000000000000), orderedInterval (37390838509 / 1000000000000) (37390838510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (961993688979353 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29866215276 / 1000000000000) (29866223357 / 1000000000000), orderedInterval (-41955959807 / 1000000000000) (-41955951726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (311088993608249 / 800000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3589461855 / 1000000000000) (3589461856 / 1000000000000), orderedInterval (40297441116 / 1000000000000) (40297441117 / 1000000000000)))) (orderedInterval (9776669005 / 1000000000000) (9776669104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (280707359197771 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91674993336 / 1000000000000) (91674994405 / 1000000000000), orderedInterval (-26482381639 / 1000000000000) (-26482380570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (754019451561487 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41446067917 / 1000000000000) (41446067918 / 1000000000000), orderedInterval (40626160992 / 1000000000000) (40626160993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2047309488661779 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17917927873 / 1000000000000) (-17917927872 / 1000000000000), orderedInterval (-30359551804 / 1000000000000) (-30359551803 / 1000000000000)))) (orderedInterval (1792438653 / 1000000000000) (1792438704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1508038903123627 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29583009422 / 1000000000000) (29583009423 / 1000000000000), orderedInterval (28481785727 / 1000000000000) (28481785728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2584050364202071 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-11360359297 / 1000000000000) (-11360359269 / 1000000000000), orderedInterval (29273152742 / 1000000000000) (29273152770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1903399802729989 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28353504769 / 1000000000000) (-28353471170 / 1000000000000), orderedInterval (23136868844 / 1000000000000) (23136902443 / 1000000000000)))) (orderedInterval (-334849346 / 1000000000000) (-334848514 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks0_1 :
    compactCertificate455.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2920304778614347 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26702581224 / 1000000000000) (26702672102 / 1000000000000), orderedInterval (-12626282314 / 1000000000000) (-12626191436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1686038750048563 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37660370183 / 1000000000000) (37660370191 / 1000000000000), orderedInterval (9548452833 / 1000000000000) (9548452842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2991905349114767 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25485919426 / 1000000000000) (25485919428 / 1000000000000), orderedInterval (14181226988 / 1000000000000) (14181226991 / 1000000000000)))) (orderedInterval (1668554644 / 1000000000000) (1668570922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2795426076897323 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24255997194 / 1000000000000) (24256015275 / 1000000000000), orderedInterval (-17978180564 / 1000000000000) (-17978162484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1994947952536859 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-318105445 / 1000000000000) (-318105444 / 1000000000000), orderedInterval (-35725909175 / 1000000000000) (-35725909174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2262058354684461 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24372589481 / 1000000000000) (24372589482 / 1000000000000), orderedInterval (23037336977 / 1000000000000) (23037336978 / 1000000000000)))) (orderedInterval (-591316253 / 1000000000000) (-591315888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1885868424697309 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31183107552 / 1000000000000) (31183107553 / 1000000000000), orderedInterval (19406803029 / 1000000000000) (19406803030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1666221945871489 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18441068744 / 1000000000000) (18441069469 / 1000000000000), orderedInterval (-34492743764 / 1000000000000) (-34492743040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (482936064033411 / 800000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31011266140 / 1000000000000) (31011266156 / 1000000000000), orderedInterval (9611915701 / 1000000000000) (9611915717 / 1000000000000)))) (orderedInterval (98782001 / 1000000000000) (98782075 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks0_2 :
    compactCertificate455.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1335826568649017 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43089099329 / 1000000000000) (43089100678 / 1000000000000), orderedInterval (-7108810499 / 1000000000000) (-7108809150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1132394976117937 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43095475755 / 1000000000000) (43095475756 / 1000000000000), orderedInterval (19711076227 / 1000000000000) (19711076228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (708600197270011 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54370409450 / 1000000000000) (54370420203 / 1000000000000), orderedInterval (-25402702591 / 1000000000000) (-25402691838 / 1000000000000)))) (orderedInterval (-7558780190 / 1000000000000) (-7558779542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (381087542789637 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79451161581 / 1000000000000) (79451162374 / 1000000000000), orderedInterval (-19641106275 / 1000000000000) (-19641105482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1034726810759911 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (47604328996 / 1000000000000) (47604332497 / 1000000000000), orderedInterval (-14050513042 / 1000000000000) (-14050509541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1412830998576647 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35887954323 / 1000000000000) (35888033652 / 1000000000000), orderedInterval (-22732237137 / 1000000000000) (-22732157808 / 1000000000000)))) (orderedInterval (-5297486296 / 1000000000000) (-5297480083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (597399802729989 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40129204224 / 1000000000000) (-40129184978 / 1000000000000), orderedInterval (51634412772 / 1000000000000) (51634432018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2428397031452069 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32379431252 / 1000000000000) (-32379430386 / 1000000000000), orderedInterval (-417877046 / 1000000000000) (-417876179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1622056675223371 / 4000000000000) 0 (IntervalRat.scale (653 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34045336059 / 1000000000000) (-34045336058 / 1000000000000), orderedInterval (-20226769354 / 1000000000000) (-20226769353 / 1000000000000)))) (orderedInterval (8781639286 / 1000000000000) (8781639563 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks0 :
    compactCertificate455.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate455.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate455_chunkChecks0_0
    compactCertificate455_chunkChecks0_1 compactCertificate455_chunkChecks0_2

theorem compactCertificate455_chunkChecks1_0 :
    compactCertificate455.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (653 / 2) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23432291653 / 1000000000000) (23432291654 / 1000000000000), orderedInterval (37390838509 / 1000000000000) (37390838510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (961993688979353 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29866215276 / 1000000000000) (29866223357 / 1000000000000), orderedInterval (-41955959807 / 1000000000000) (-41955951726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (311088993608249 / 800000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3589461855 / 1000000000000) (3589461856 / 1000000000000), orderedInterval (40297441116 / 1000000000000) (40297441117 / 1000000000000)))) (orderedInterval (17348804366 / 1000000000000) (17348804448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (280707359197771 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91674993336 / 1000000000000) (91674994405 / 1000000000000), orderedInterval (-26482381639 / 1000000000000) (-26482380570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (754019451561487 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41446067917 / 1000000000000) (41446067918 / 1000000000000), orderedInterval (40626160992 / 1000000000000) (40626160993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2047309488661779 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17917927873 / 1000000000000) (-17917927872 / 1000000000000), orderedInterval (-30359551804 / 1000000000000) (-30359551803 / 1000000000000)))) (orderedInterval (4301468315 / 1000000000000) (4301468362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1508038903123627 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29583009422 / 1000000000000) (29583009423 / 1000000000000), orderedInterval (28481785727 / 1000000000000) (28481785728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2584050364202071 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-11360359297 / 1000000000000) (-11360359269 / 1000000000000), orderedInterval (29273152742 / 1000000000000) (29273152770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1903399802729989 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28353504769 / 1000000000000) (-28353471170 / 1000000000000), orderedInterval (23136868844 / 1000000000000) (23136902443 / 1000000000000)))) (orderedInterval (-971526267 / 1000000000000) (-971525049 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks1_1 :
    compactCertificate455.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2920304778614347 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26702581224 / 1000000000000) (26702672102 / 1000000000000), orderedInterval (-12626282314 / 1000000000000) (-12626191436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1686038750048563 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37660370183 / 1000000000000) (37660370191 / 1000000000000), orderedInterval (9548452833 / 1000000000000) (9548452842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2991905349114767 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25485919426 / 1000000000000) (25485919428 / 1000000000000), orderedInterval (14181226988 / 1000000000000) (14181226991 / 1000000000000)))) (orderedInterval (10548309105 / 1000000000000) (10548345483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2795426076897323 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24255997194 / 1000000000000) (24256015275 / 1000000000000), orderedInterval (-17978180564 / 1000000000000) (-17978162484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1994947952536859 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-318105445 / 1000000000000) (-318105444 / 1000000000000), orderedInterval (-35725909175 / 1000000000000) (-35725909174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2262058354684461 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24372589481 / 1000000000000) (24372589482 / 1000000000000), orderedInterval (23037336977 / 1000000000000) (23037336978 / 1000000000000)))) (orderedInterval (-4667725710 / 1000000000000) (-4667724948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1885868424697309 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31183107552 / 1000000000000) (31183107553 / 1000000000000), orderedInterval (19406803029 / 1000000000000) (19406803030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1666221945871489 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18441068744 / 1000000000000) (18441069469 / 1000000000000), orderedInterval (-34492743764 / 1000000000000) (-34492743040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (482936064033411 / 800000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31011266140 / 1000000000000) (31011266156 / 1000000000000), orderedInterval (9611915701 / 1000000000000) (9611915717 / 1000000000000)))) (orderedInterval (3296978136 / 1000000000000) (3296978236 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks1_2 :
    compactCertificate455.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1335826568649017 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43089099329 / 1000000000000) (43089100678 / 1000000000000), orderedInterval (-7108810499 / 1000000000000) (-7108809150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1132394976117937 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43095475755 / 1000000000000) (43095475756 / 1000000000000), orderedInterval (19711076227 / 1000000000000) (19711076228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (708600197270011 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54370409450 / 1000000000000) (54370420203 / 1000000000000), orderedInterval (-25402702591 / 1000000000000) (-25402691838 / 1000000000000)))) (orderedInterval (-253444282 / 1000000000000) (-253443796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (381087542789637 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79451161581 / 1000000000000) (79451162374 / 1000000000000), orderedInterval (-19641106275 / 1000000000000) (-19641105482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1034726810759911 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (47604328996 / 1000000000000) (47604332497 / 1000000000000), orderedInterval (-14050513042 / 1000000000000) (-14050509541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1412830998576647 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35887954323 / 1000000000000) (35888033652 / 1000000000000), orderedInterval (-22732237137 / 1000000000000) (-22732157808 / 1000000000000)))) (orderedInterval (2243055100 / 1000000000000) (2243061779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (597399802729989 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40129204224 / 1000000000000) (-40129184978 / 1000000000000), orderedInterval (51634412772 / 1000000000000) (51634432018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2428397031452069 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32379431252 / 1000000000000) (-32379430386 / 1000000000000), orderedInterval (-417877046 / 1000000000000) (-417876179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1622056675223371 / 4000000000000) 1 (IntervalRat.scale (653 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34045336059 / 1000000000000) (-34045336058 / 1000000000000), orderedInterval (-20226769354 / 1000000000000) (-20226769353 / 1000000000000)))) (orderedInterval (4919133595 / 1000000000000) (4919133907 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks1 :
    compactCertificate455.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate455.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate455_chunkChecks1_0
    compactCertificate455_chunkChecks1_1 compactCertificate455_chunkChecks1_2

theorem compactCertificate455_chunkChecks2_0 :
    compactCertificate455.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (653 / 2) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23432291653 / 1000000000000) (23432291654 / 1000000000000), orderedInterval (37390838509 / 1000000000000) (37390838510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (961993688979353 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29866215276 / 1000000000000) (29866223357 / 1000000000000), orderedInterval (-41955959807 / 1000000000000) (-41955951726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (311088993608249 / 800000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3589461855 / 1000000000000) (3589461856 / 1000000000000), orderedInterval (40297441116 / 1000000000000) (40297441117 / 1000000000000)))) (orderedInterval (-9790650817 / 1000000000000) (-9790650745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (280707359197771 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91674993336 / 1000000000000) (91674994405 / 1000000000000), orderedInterval (-26482381639 / 1000000000000) (-26482380570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (754019451561487 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41446067917 / 1000000000000) (41446067918 / 1000000000000), orderedInterval (40626160992 / 1000000000000) (40626160993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2047309488661779 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17917927873 / 1000000000000) (-17917927872 / 1000000000000), orderedInterval (-30359551804 / 1000000000000) (-30359551803 / 1000000000000)))) (orderedInterval (-3601867745 / 1000000000000) (-3601867682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1508038903123627 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29583009422 / 1000000000000) (29583009423 / 1000000000000), orderedInterval (28481785727 / 1000000000000) (28481785728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2584050364202071 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-11360359297 / 1000000000000) (-11360359269 / 1000000000000), orderedInterval (29273152742 / 1000000000000) (29273152770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1903399802729989 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28353504769 / 1000000000000) (-28353471170 / 1000000000000), orderedInterval (23136868844 / 1000000000000) (23136902443 / 1000000000000)))) (orderedInterval (86744661 / 1000000000000) (86746450 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks2_1 :
    compactCertificate455.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2920304778614347 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26702581224 / 1000000000000) (26702672102 / 1000000000000), orderedInterval (-12626282314 / 1000000000000) (-12626191436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1686038750048563 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37660370183 / 1000000000000) (37660370191 / 1000000000000), orderedInterval (9548452833 / 1000000000000) (9548452842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2991905349114767 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25485919426 / 1000000000000) (25485919428 / 1000000000000), orderedInterval (14181226988 / 1000000000000) (14181226991 / 1000000000000)))) (orderedInterval (26739564 / 1000000000000) (26820991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2795426076897323 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24255997194 / 1000000000000) (24256015275 / 1000000000000), orderedInterval (-17978180564 / 1000000000000) (-17978162484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1994947952536859 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-318105445 / 1000000000000) (-318105444 / 1000000000000), orderedInterval (-35725909175 / 1000000000000) (-35725909174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2262058354684461 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24372589481 / 1000000000000) (24372589482 / 1000000000000), orderedInterval (23037336977 / 1000000000000) (23037336978 / 1000000000000)))) (orderedInterval (2460730983 / 1000000000000) (2460732586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1885868424697309 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31183107552 / 1000000000000) (31183107553 / 1000000000000), orderedInterval (19406803029 / 1000000000000) (19406803030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1666221945871489 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18441068744 / 1000000000000) (18441069469 / 1000000000000), orderedInterval (-34492743764 / 1000000000000) (-34492743040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (482936064033411 / 800000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31011266140 / 1000000000000) (31011266156 / 1000000000000), orderedInterval (9611915701 / 1000000000000) (9611915717 / 1000000000000)))) (orderedInterval (-1757486653 / 1000000000000) (-1757486516 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks2_2 :
    compactCertificate455.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1335826568649017 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43089099329 / 1000000000000) (43089100678 / 1000000000000), orderedInterval (-7108810499 / 1000000000000) (-7108809150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1132394976117937 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43095475755 / 1000000000000) (43095475756 / 1000000000000), orderedInterval (19711076227 / 1000000000000) (19711076228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (708600197270011 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54370409450 / 1000000000000) (54370420203 / 1000000000000), orderedInterval (-25402702591 / 1000000000000) (-25402691838 / 1000000000000)))) (orderedInterval (8521430350 / 1000000000000) (8521430753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (381087542789637 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79451161581 / 1000000000000) (79451162374 / 1000000000000), orderedInterval (-19641106275 / 1000000000000) (-19641105482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1034726810759911 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (47604328996 / 1000000000000) (47604332497 / 1000000000000), orderedInterval (-14050513042 / 1000000000000) (-14050509541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1412830998576647 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35887954323 / 1000000000000) (35888033652 / 1000000000000), orderedInterval (-22732237137 / 1000000000000) (-22732157808 / 1000000000000)))) (orderedInterval (4014761177 / 1000000000000) (4014768399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (597399802729989 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40129204224 / 1000000000000) (-40129184978 / 1000000000000), orderedInterval (51634412772 / 1000000000000) (51634432018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2428397031452069 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32379431252 / 1000000000000) (-32379430386 / 1000000000000), orderedInterval (-417877046 / 1000000000000) (-417876179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1622056675223371 / 4000000000000) 2 (IntervalRat.scale (653 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34045336059 / 1000000000000) (-34045336058 / 1000000000000), orderedInterval (-20226769354 / 1000000000000) (-20226769353 / 1000000000000)))) (orderedInterval (-18930998668 / 1000000000000) (-18930998211 / 1000000000000))) = true
  rfl'

theorem compactCertificate455_chunkChecks2 :
    compactCertificate455.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate455.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate455_chunkChecks2_0
    compactCertificate455_chunkChecks2_1 compactCertificate455_chunkChecks2_2

theorem compactCertificate455_chunkChecks3_0 :
    compactCertificate455.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (653 / 2) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23432291653 / 1000000000000) (23432291654 / 1000000000000), orderedInterval (37390838509 / 1000000000000) (37390838510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (961993688979353 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29866215276 / 1000000000000) (29866223357 / 1000000000000), orderedInterval (-41955959807 / 1000000000000) (-41955951726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (311088993608249 / 800000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3589461855 / 1000000000000) (3589461856 / 1000000000000), orderedInterval (40297441116 / 1000000000000) (40297441117 / 1000000000000)))) (orderedInterval (-18628966577 / 1000000000000) (-18628966512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (280707359197771 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91674993336 / 1000000000000) (91674994405 / 1000000000000), orderedInterval (-26482381639 / 1000000000000) (-26482380570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (754019451561487 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41446067917 / 1000000000000) (41446067918 / 1000000000000), orderedInterval (40626160992 / 1000000000000) (40626160993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2047309488661779 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17917927873 / 1000000000000) (-17917927872 / 1000000000000), orderedInterval (-30359551804 / 1000000000000) (-30359551803 / 1000000000000)))) (orderedInterval (-8591489923 / 1000000000000) (-8591489830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1508038903123627 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29583009422 / 1000000000000) (29583009423 / 1000000000000), orderedInterval (28481785727 / 1000000000000) (28481785728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2584050364202071 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-11360359297 / 1000000000000) (-11360359269 / 1000000000000), orderedInterval (29273152742 / 1000000000000) (29273152770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1903399802729989 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28353504769 / 1000000000000) (-28353471170 / 1000000000000), orderedInterval (23136868844 / 1000000000000) (23136902443 / 1000000000000)))) (orderedInterval (5262492069 / 1000000000000) (5262494698 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate455_chunkChecks3_1 :
    compactCertificate455.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2920304778614347 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26702581224 / 1000000000000) (26702672102 / 1000000000000), orderedInterval (-12626282314 / 1000000000000) (-12626191436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1686038750048563 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37660370183 / 1000000000000) (37660370191 / 1000000000000), orderedInterval (9548452833 / 1000000000000) (9548452842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2991905349114767 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25485919426 / 1000000000000) (25485919428 / 1000000000000), orderedInterval (14181226988 / 1000000000000) (14181226991 / 1000000000000)))) (orderedInterval (-50843487535 / 1000000000000) (-50843305483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2795426076897323 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24255997194 / 1000000000000) (24256015275 / 1000000000000), orderedInterval (-17978180564 / 1000000000000) (-17978162484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1994947952536859 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-318105445 / 1000000000000) (-318105444 / 1000000000000), orderedInterval (-35725909175 / 1000000000000) (-35725909174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2262058354684461 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24372589481 / 1000000000000) (24372589482 / 1000000000000), orderedInterval (23037336977 / 1000000000000) (23037336978 / 1000000000000)))) (orderedInterval (9456562351 / 1000000000000) (9456565734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1885868424697309 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31183107552 / 1000000000000) (31183107553 / 1000000000000), orderedInterval (19406803029 / 1000000000000) (19406803030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1666221945871489 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18441068744 / 1000000000000) (18441069469 / 1000000000000), orderedInterval (-34492743764 / 1000000000000) (-34492743040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (482936064033411 / 800000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31011266140 / 1000000000000) (31011266156 / 1000000000000), orderedInterval (9611915701 / 1000000000000) (9611915717 / 1000000000000)))) (orderedInterval (-6324002755 / 1000000000000) (-6324002562 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate455_chunkChecks3_2 :
    compactCertificate455.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1335826568649017 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43089099329 / 1000000000000) (43089100678 / 1000000000000), orderedInterval (-7108810499 / 1000000000000) (-7108809150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1132394976117937 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43095475755 / 1000000000000) (43095475756 / 1000000000000), orderedInterval (19711076227 / 1000000000000) (19711076228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (708600197270011 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54370409450 / 1000000000000) (54370420203 / 1000000000000), orderedInterval (-25402702591 / 1000000000000) (-25402691838 / 1000000000000)))) (orderedInterval (-383062055 / 1000000000000) (-383061697 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (381087542789637 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79451161581 / 1000000000000) (79451162374 / 1000000000000), orderedInterval (-19641106275 / 1000000000000) (-19641105482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1034726810759911 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (47604328996 / 1000000000000) (47604332497 / 1000000000000), orderedInterval (-14050513042 / 1000000000000) (-14050509541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1412830998576647 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35887954323 / 1000000000000) (35888033652 / 1000000000000), orderedInterval (-22732237137 / 1000000000000) (-22732157808 / 1000000000000)))) (orderedInterval (-2385445743 / 1000000000000) (-2385437948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (597399802729989 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40129204224 / 1000000000000) (-40129184978 / 1000000000000), orderedInterval (51634412772 / 1000000000000) (51634432018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2428397031452069 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32379431252 / 1000000000000) (-32379430386 / 1000000000000), orderedInterval (-417877046 / 1000000000000) (-417876179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1622056675223371 / 4000000000000) 3 (IntervalRat.scale (653 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34045336059 / 1000000000000) (-34045336058 / 1000000000000), orderedInterval (-20226769354 / 1000000000000) (-20226769353 / 1000000000000)))) (orderedInterval (-7461364965 / 1000000000000) (-7461364209 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate455_chunkChecks3 :
    compactCertificate455.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate455.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate455_chunkChecks3_0
    compactCertificate455_chunkChecks3_1 compactCertificate455_chunkChecks3_2

theorem compactCertificate455_chunkChecks4_0 :
    compactCertificate455.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (653 / 2) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23432291653 / 1000000000000) (23432291654 / 1000000000000), orderedInterval (37390838509 / 1000000000000) (37390838510 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (961993688979353 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29866215276 / 1000000000000) (29866223357 / 1000000000000), orderedInterval (-41955959807 / 1000000000000) (-41955951726 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (311088993608249 / 800000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3589461855 / 1000000000000) (3589461856 / 1000000000000), orderedInterval (40297441116 / 1000000000000) (40297441117 / 1000000000000)))) (orderedInterval (9907499414 / 1000000000000) (9907499477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (280707359197771 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91674993336 / 1000000000000) (91674994405 / 1000000000000), orderedInterval (-26482381639 / 1000000000000) (-26482380570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (754019451561487 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (41446067917 / 1000000000000) (41446067918 / 1000000000000), orderedInterval (40626160992 / 1000000000000) (40626160993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2047309488661779 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-17917927873 / 1000000000000) (-17917927872 / 1000000000000), orderedInterval (-30359551804 / 1000000000000) (-30359551803 / 1000000000000)))) (orderedInterval (7910897513 / 1000000000000) (7910897656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1508038903123627 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29583009422 / 1000000000000) (29583009423 / 1000000000000), orderedInterval (28481785727 / 1000000000000) (28481785728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2584050364202071 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-11360359297 / 1000000000000) (-11360359269 / 1000000000000), orderedInterval (29273152742 / 1000000000000) (29273152770 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1903399802729989 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28353504769 / 1000000000000) (-28353471170 / 1000000000000), orderedInterval (23136868844 / 1000000000000) (23136902443 / 1000000000000)))) (orderedInterval (2246322683 / 1000000000000) (2246326567 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate455_chunkChecks4_1 :
    compactCertificate455.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2920304778614347 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26702581224 / 1000000000000) (26702672102 / 1000000000000), orderedInterval (-12626282314 / 1000000000000) (-12626191436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1686038750048563 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37660370183 / 1000000000000) (37660370191 / 1000000000000), orderedInterval (9548452833 / 1000000000000) (9548452842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2991905349114767 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25485919426 / 1000000000000) (25485919428 / 1000000000000), orderedInterval (14181226988 / 1000000000000) (14181226991 / 1000000000000)))) (orderedInterval (-10766944783 / 1000000000000) (-10766537174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2795426076897323 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24255997194 / 1000000000000) (24256015275 / 1000000000000), orderedInterval (-17978180564 / 1000000000000) (-17978162484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1994947952536859 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-318105445 / 1000000000000) (-318105444 / 1000000000000), orderedInterval (-35725909175 / 1000000000000) (-35725909174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2262058354684461 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24372589481 / 1000000000000) (24372589482 / 1000000000000), orderedInterval (23037336977 / 1000000000000) (23037336978 / 1000000000000)))) (orderedInterval (-10523313679 / 1000000000000) (-10523306500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1885868424697309 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (31183107552 / 1000000000000) (31183107553 / 1000000000000), orderedInterval (19406803029 / 1000000000000) (19406803030 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1666221945871489 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18441068744 / 1000000000000) (18441069469 / 1000000000000), orderedInterval (-34492743764 / 1000000000000) (-34492743040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (482936064033411 / 800000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31011266140 / 1000000000000) (31011266156 / 1000000000000), orderedInterval (9611915701 / 1000000000000) (9611915717 / 1000000000000)))) (orderedInterval (8087113773 / 1000000000000) (8087114053 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate455_chunkChecks4_2 :
    compactCertificate455.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1335826568649017 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43089099329 / 1000000000000) (43089100678 / 1000000000000), orderedInterval (-7108810499 / 1000000000000) (-7108809150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1132394976117937 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43095475755 / 1000000000000) (43095475756 / 1000000000000), orderedInterval (19711076227 / 1000000000000) (19711076228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (708600197270011 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54370409450 / 1000000000000) (54370420203 / 1000000000000), orderedInterval (-25402702591 / 1000000000000) (-25402691838 / 1000000000000)))) (orderedInterval (-8763763631 / 1000000000000) (-8763763293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (381087542789637 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (79451161581 / 1000000000000) (79451162374 / 1000000000000), orderedInterval (-19641106275 / 1000000000000) (-19641105482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1034726810759911 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (47604328996 / 1000000000000) (47604332497 / 1000000000000), orderedInterval (-14050513042 / 1000000000000) (-14050509541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1412830998576647 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35887954323 / 1000000000000) (35888033652 / 1000000000000), orderedInterval (-22732237137 / 1000000000000) (-22732157808 / 1000000000000)))) (orderedInterval (-4188461098 / 1000000000000) (-4188452655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (597399802729989 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40129204224 / 1000000000000) (-40129184978 / 1000000000000), orderedInterval (51634412772 / 1000000000000) (51634432018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2428397031452069 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32379431252 / 1000000000000) (-32379430386 / 1000000000000), orderedInterval (-417877046 / 1000000000000) (-417876179 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1622056675223371 / 4000000000000) 4 (IntervalRat.scale (653 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34045336059 / 1000000000000) (-34045336058 / 1000000000000), orderedInterval (-20226769354 / 1000000000000) (-20226769353 / 1000000000000)))) (orderedInterval (46742076893 / 1000000000000) (46742078208 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate455_chunkChecks4 :
    compactCertificate455.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate455.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate455_chunkChecks4_0
    compactCertificate455_chunkChecks4_1 compactCertificate455_chunkChecks4_2

theorem compactCertificate455_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate455.chunkCheck r b = true :=
  compactCertificate455.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate455_chunkChecks0
    · exact compactCertificate455_chunkChecks1
    · exact compactCertificate455_chunkChecks2
    · exact compactCertificate455_chunkChecks3
    · exact compactCertificate455_chunkChecks4)

theorem compactCertificate455_coefficient0 :
    compactCertificate455.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate455_coefficient1 :
    compactCertificate455.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate455_coefficient2 :
    compactCertificate455.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate455_coefficient3 :
    compactCertificate455.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate455_coefficient4 :
    compactCertificate455.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate455_coefficients : ∀ r : Fin 5,
    compactCertificate455.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate455_coefficient0
  · exact compactCertificate455_coefficient1
  · exact compactCertificate455_coefficient2
  · exact compactCertificate455_coefficient3
  · exact compactCertificate455_coefficient4

theorem compactCertificate455_lower : (1 : ℚ) ≤ compactCertificate455.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate455, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate455_proves {t : ℝ} (ht : t ∈ compactCertificate455.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate455.proves compactCertificate455_states compactCertificate455_chunks
    compactCertificate455_coefficients compactCertificate455_lower ht

end Erdos232
