/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate388 : CompactCertificate where
  left := 259
  right := 260
  center := 519 / 2
  grid := fun i =>
    match i.val with
    | 0 => 83
    | 1 => 61
    | 2 => 98
    | 3 => 18
    | 4 => 48
    | 5 => 130
    | 6 => 95
    | 7 => 164
    | 8 => 120
    | 9 => 185
    | 10 => 107
    | 11 => 189
    | 12 => 177
    | 13 => 126
    | 14 => 143
    | 15 => 119
    | 16 => 105
    | 17 => 153
    | 18 => 85
    | 19 => 72
    | 20 => 45
    | 21 => 24
    | 22 => 65
    | 23 => 89
    | 24 => 38
    | 25 => 154
    | _ => 103
  point := fun i =>
    match i.val with
    | 0 => 519 / 2
    | 1 => 764586101960619 / 4000000000000
    | 2 => 247251435961227 / 800000000000
    | 3 => 223104317647233 / 4000000000000
    | 4 => 599289579418701 / 4000000000000
    | 5 => 1627187786547417 / 4000000000000
    | 6 => 1198579158837921 / 4000000000000
    | 7 => 2053785817796133 / 4000000000000
    | 8 => 1512809337851247 / 4000000000000
    | 9 => 2321038560644481 / 4000000000000
    | 10 => 1340052237787449 / 4000000000000
    | 11 => 2377946211624141 / 4000000000000
    | 12 => 2221785809968929 / 4000000000000
    | 13 => 1585571190454257 / 4000000000000
    | 14 => 1797868738256103 / 4000000000000
    | 15 => 1498875516719607 / 4000000000000
    | 16 => 1324301975355747 / 4000000000000
    | 17 => 383834329606953 / 800000000000
    | 18 => 1061705955786891 / 4000000000000
    | 19 => 900019896792051 / 4000000000000
    | 20 => 563190662148753 / 4000000000000
    | 21 => 302885811191151 / 4000000000000
    | 22 => 822393897066453 / 4000000000000
    | 23 => 1122908557827381 / 4000000000000
    | 24 => 474809337851247 / 4000000000000
    | 25 => 1930073597739087 / 4000000000000
    | _ => 1289199715836033 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (22311121544 / 1000000000000) (22311122946 / 1000000000000), orderedInterval (-44263707345 / 1000000000000) (-44263705942 / 1000000000000))
    | 1 => (orderedInterval (-16730074408 / 1000000000000) (-16730074407 / 1000000000000), orderedInterval (-55188899282 / 1000000000000) (-55188899281 / 1000000000000))
    | 2 => (orderedInterval (41759879977 / 1000000000000) (41759895016 / 1000000000000), orderedInterval (-17842251965 / 1000000000000) (-17842236926 / 1000000000000))
    | 3 => (orderedInterval (1129110643 / 1000000000000) (1129110651 / 1000000000000), orderedInterval (106821675861 / 1000000000000) (106821675869 / 1000000000000))
    | 4 => (orderedInterval (-12278112965 / 1000000000000) (-12278112885 / 1000000000000), orderedInterval (64059979235 / 1000000000000) (64059979315 / 1000000000000))
    | 5 => (orderedInterval (-29058572963 / 1000000000000) (-29058546737 / 1000000000000), orderedInterval (26878897284 / 1000000000000) (26878923510 / 1000000000000))
    | 6 => (orderedInterval (-42315648160 / 1000000000000) (-42315633049 / 1000000000000), orderedInterval (18345338236 / 1000000000000) (18345353347 / 1000000000000))
    | 7 => (orderedInterval (-29430294362 / 1000000000000) (-29430224104 / 1000000000000), orderedInterval (19361360325 / 1000000000000) (19361430583 / 1000000000000))
    | 8 => (orderedInterval (37369612958 / 1000000000000) (37369639010 / 1000000000000), orderedInterval (-16984242725 / 1000000000000) (-16984216674 / 1000000000000))
    | 9 => (orderedInterval (4943868958 / 1000000000000) (4943868960 / 1000000000000), orderedInterval (-32756171597 / 1000000000000) (-32756171595 / 1000000000000))
    | 10 => (orderedInterval (15043023792 / 1000000000000) (15043024001 / 1000000000000), orderedInterval (-40936904816 / 1000000000000) (-40936904608 / 1000000000000))
    | 11 => (orderedInterval (-32665177319 / 1000000000000) (-32665176866 / 1000000000000), orderedInterval (-1936991564 / 1000000000000) (-1936991111 / 1000000000000))
    | 12 => (orderedInterval (-5718471285 / 1000000000000) (-5718471284 / 1000000000000), orderedInterval (-33363103743 / 1000000000000) (-33363103742 / 1000000000000))
    | 13 => (orderedInterval (38986940602 / 1000000000000) (38986940611 / 1000000000000), orderedInterval (9227134916 / 1000000000000) (9227134925 / 1000000000000))
    | 14 => (orderedInterval (-31760985224 / 1000000000000) (-31760985223 / 1000000000000), orderedInterval (-20154445406 / 1000000000000) (-20154445405 / 1000000000000))
    | 15 => (orderedInterval (-41073989878 / 1000000000000) (-41073989201 / 1000000000000), orderedInterval (3497512302 / 1000000000000) (3497512978 / 1000000000000))
    | 16 => (orderedInterval (-39994939800 / 1000000000000) (-39994919536 / 1000000000000), orderedInterval (18040605823 / 1000000000000) (18040626087 / 1000000000000))
    | 17 => (orderedInterval (3115226735 / 1000000000000) (3115226737 / 1000000000000), orderedInterval (-36295941530 / 1000000000000) (-36295941528 / 1000000000000))
    | 18 => (orderedInterval (35939279220 / 1000000000000) (35939328806 / 1000000000000), orderedInterval (-33337000523 / 1000000000000) (-33336950938 / 1000000000000))
    | 19 => (orderedInterval (-20951382072 / 1000000000000) (-20951381248 / 1000000000000), orderedInterval (48938305573 / 1000000000000) (48938306396 / 1000000000000))
    | 20 => (orderedInterval (-14050580623 / 1000000000000) (-14050580622 / 1000000000000), orderedInterval (-65708217209 / 1000000000000) (-65708217208 / 1000000000000))
    | 21 => (orderedInterval (82003705769 / 1000000000000) (82003705770 / 1000000000000), orderedInterval (40478928362 / 1000000000000) (40478928363 / 1000000000000))
    | 22 => (orderedInterval (-45643277986 / 1000000000000) (-45643216298 / 1000000000000), orderedInterval (31940410035 / 1000000000000) (31940471722 / 1000000000000))
    | 23 => (orderedInterval (-44901964720 / 1000000000000) (-44901957745 / 1000000000000), orderedInterval (15940737352 / 1000000000000) (15940744326 / 1000000000000))
    | 24 => (orderedInterval (7759761401 / 1000000000000) (7759761403 / 1000000000000), orderedInterval (72788973359 / 1000000000000) (72788973361 / 1000000000000))
    | 25 => (orderedInterval (-17469349883 / 1000000000000) (-17469349336 / 1000000000000), orderedInterval (31864469257 / 1000000000000) (31864469804 / 1000000000000))
    | _ => (orderedInterval (21272465032 / 1000000000000) (21272466435 / 1000000000000), orderedInterval (-39055093807 / 1000000000000) (-39055092403 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11137973051 / 1000000000000) (11137974508 / 1000000000000)
      | 1 => orderedInterval (1605216248 / 1000000000000) (1605218147 / 1000000000000)
      | 2 => orderedInterval (1810895669 / 1000000000000) (1810898481 / 1000000000000)
      | 3 => orderedInterval (-4407449019 / 1000000000000) (-4407448835 / 1000000000000)
      | 4 => orderedInterval (3950681758 / 1000000000000) (3950681790 / 1000000000000)
      | 5 => orderedInterval (1894229558 / 1000000000000) (1894230751 / 1000000000000)
      | 6 => orderedInterval (-5018000283 / 1000000000000) (-5017992242 / 1000000000000)
      | 7 => orderedInterval (2962528614 / 1000000000000) (2962530580 / 1000000000000)
      | _ => orderedInterval (-2522464568 / 1000000000000) (-2522464188 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-19170361407 / 1000000000000) (-19170359778 / 1000000000000)
      | 1 => orderedInterval (-1894135495 / 1000000000000) (-1894132535 / 1000000000000)
      | 2 => orderedInterval (-1779825999 / 1000000000000) (-1779820768 / 1000000000000)
      | 3 => orderedInterval (8468249127 / 1000000000000) (8468249509 / 1000000000000)
      | 4 => orderedInterval (2798697908 / 1000000000000) (2798697960 / 1000000000000)
      | 5 => orderedInterval (-2977074114 / 1000000000000) (-2977072586 / 1000000000000)
      | 6 => orderedInterval (1889711187 / 1000000000000) (1889719398 / 1000000000000)
      | 7 => orderedInterval (-2113832002 / 1000000000000) (-2113830287 / 1000000000000)
      | _ => orderedInterval (4478837107 / 1000000000000) (4478837619 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12160900158 / 1000000000000) (-12160898320 / 1000000000000)
      | 1 => orderedInterval (-4919166430 / 1000000000000) (-4919161786 / 1000000000000)
      | 2 => orderedInterval (-5465218802 / 1000000000000) (-5465208915 / 1000000000000)
      | 3 => orderedInterval (26872296194 / 1000000000000) (26872297017 / 1000000000000)
      | 4 => orderedInterval (-9568289075 / 1000000000000) (-9568288990 / 1000000000000)
      | 5 => orderedInterval (-2997675531 / 1000000000000) (-2997673567 / 1000000000000)
      | 6 => orderedInterval (5247731935 / 1000000000000) (5247740354 / 1000000000000)
      | 7 => orderedInterval (-4540179505 / 1000000000000) (-4540177966 / 1000000000000)
      | _ => orderedInterval (1213204686 / 1000000000000) (1213205398 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (19565500872 / 1000000000000) (19565502954 / 1000000000000)
      | 1 => orderedInterval (6941338920 / 1000000000000) (6941346195 / 1000000000000)
      | 2 => orderedInterval (5917473076 / 1000000000000) (5917491931 / 1000000000000)
      | 3 => orderedInterval (-55340448749 / 1000000000000) (-55340446935 / 1000000000000)
      | 4 => orderedInterval (-9509532803 / 1000000000000) (-9509532659 / 1000000000000)
      | 5 => orderedInterval (7907606506 / 1000000000000) (7907609029 / 1000000000000)
      | 6 => orderedInterval (-3576828379 / 1000000000000) (-3576819777 / 1000000000000)
      | 7 => orderedInterval (1943089950 / 1000000000000) (1943091357 / 1000000000000)
      | _ => orderedInterval (2589418855 / 1000000000000) (2589419878 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (13577126244 / 1000000000000) (13577128624 / 1000000000000)
      | 1 => orderedInterval (12371619611 / 1000000000000) (12371631039 / 1000000000000)
      | 2 => orderedInterval (17941309074 / 1000000000000) (17941345423 / 1000000000000)
      | 3 => orderedInterval (-146338141110 / 1000000000000) (-146338137055 / 1000000000000)
      | 4 => orderedInterval (23758792968 / 1000000000000) (23758793218 / 1000000000000)
      | 5 => orderedInterval (4872934705 / 1000000000000) (4872937962 / 1000000000000)
      | 6 => orderedInterval (-5631365380 / 1000000000000) (-5631356555 / 1000000000000)
      | 7 => orderedInterval (5095053830 / 1000000000000) (5095055155 / 1000000000000)
      | _ => orderedInterval (7483473998 / 1000000000000) (7483475532 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (11413611028 / 1000000000000) (11413628992 / 1000000000000)
    | 1 => orderedInterval (-10299733688 / 1000000000000) (-10299711468 / 1000000000000)
    | 2 => orderedInterval (-6318196686 / 1000000000000) (-6318166775 / 1000000000000)
    | 3 => orderedInterval (-23562381752 / 1000000000000) (-23562338027 / 1000000000000)
    | _ => orderedInterval (-66869196060 / 1000000000000) (-66869126657 / 1000000000000)

theorem compactCertificate388_stateChecks0 :
    compactCertificate388.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (519 / 2)) (orderedInterval (22311121544 / 1000000000000) (22311122946 / 1000000000000), orderedInterval (-44263707345 / 1000000000000) (-44263705942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (764586101960619 / 4000000000000)) (orderedInterval (-16730074408 / 1000000000000) (-16730074407 / 1000000000000), orderedInterval (-55188899282 / 1000000000000) (-55188899281 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (247251435961227 / 800000000000)) (orderedInterval (41759879977 / 1000000000000) (41759895016 / 1000000000000), orderedInterval (-17842251965 / 1000000000000) (-17842236926 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks1 :
    compactCertificate388.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (223104317647233 / 4000000000000)) (orderedInterval (1129110643 / 1000000000000) (1129110651 / 1000000000000), orderedInterval (106821675861 / 1000000000000) (106821675869 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (599289579418701 / 4000000000000)) (orderedInterval (-12278112965 / 1000000000000) (-12278112885 / 1000000000000), orderedInterval (64059979235 / 1000000000000) (64059979315 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1627187786547417 / 4000000000000)) (orderedInterval (-29058572963 / 1000000000000) (-29058546737 / 1000000000000), orderedInterval (26878897284 / 1000000000000) (26878923510 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks2 :
    compactCertificate388.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1198579158837921 / 4000000000000)) (orderedInterval (-42315648160 / 1000000000000) (-42315633049 / 1000000000000), orderedInterval (18345338236 / 1000000000000) (18345353347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2053785817796133 / 4000000000000)) (orderedInterval (-29430294362 / 1000000000000) (-29430224104 / 1000000000000), orderedInterval (19361360325 / 1000000000000) (19361430583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1512809337851247 / 4000000000000)) (orderedInterval (37369612958 / 1000000000000) (37369639010 / 1000000000000), orderedInterval (-16984242725 / 1000000000000) (-16984216674 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks3 :
    compactCertificate388.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2321038560644481 / 4000000000000)) (orderedInterval (4943868958 / 1000000000000) (4943868960 / 1000000000000), orderedInterval (-32756171597 / 1000000000000) (-32756171595 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1340052237787449 / 4000000000000)) (orderedInterval (15043023792 / 1000000000000) (15043024001 / 1000000000000), orderedInterval (-40936904816 / 1000000000000) (-40936904608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2377946211624141 / 4000000000000)) (orderedInterval (-32665177319 / 1000000000000) (-32665176866 / 1000000000000), orderedInterval (-1936991564 / 1000000000000) (-1936991111 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks4 :
    compactCertificate388.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2221785809968929 / 4000000000000)) (orderedInterval (-5718471285 / 1000000000000) (-5718471284 / 1000000000000), orderedInterval (-33363103743 / 1000000000000) (-33363103742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1585571190454257 / 4000000000000)) (orderedInterval (38986940602 / 1000000000000) (38986940611 / 1000000000000), orderedInterval (9227134916 / 1000000000000) (9227134925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1797868738256103 / 4000000000000)) (orderedInterval (-31760985224 / 1000000000000) (-31760985223 / 1000000000000), orderedInterval (-20154445406 / 1000000000000) (-20154445405 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks5 :
    compactCertificate388.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1498875516719607 / 4000000000000)) (orderedInterval (-41073989878 / 1000000000000) (-41073989201 / 1000000000000), orderedInterval (3497512302 / 1000000000000) (3497512978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1324301975355747 / 4000000000000)) (orderedInterval (-39994939800 / 1000000000000) (-39994919536 / 1000000000000), orderedInterval (18040605823 / 1000000000000) (18040626087 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (383834329606953 / 800000000000)) (orderedInterval (3115226735 / 1000000000000) (3115226737 / 1000000000000), orderedInterval (-36295941530 / 1000000000000) (-36295941528 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks6 :
    compactCertificate388.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1061705955786891 / 4000000000000)) (orderedInterval (35939279220 / 1000000000000) (35939328806 / 1000000000000), orderedInterval (-33337000523 / 1000000000000) (-33336950938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (900019896792051 / 4000000000000)) (orderedInterval (-20951382072 / 1000000000000) (-20951381248 / 1000000000000), orderedInterval (48938305573 / 1000000000000) (48938306396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (563190662148753 / 4000000000000)) (orderedInterval (-14050580623 / 1000000000000) (-14050580622 / 1000000000000), orderedInterval (-65708217209 / 1000000000000) (-65708217208 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks7 :
    compactCertificate388.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (302885811191151 / 4000000000000)) (orderedInterval (82003705769 / 1000000000000) (82003705770 / 1000000000000), orderedInterval (40478928362 / 1000000000000) (40478928363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (822393897066453 / 4000000000000)) (orderedInterval (-45643277986 / 1000000000000) (-45643216298 / 1000000000000), orderedInterval (31940410035 / 1000000000000) (31940471722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1122908557827381 / 4000000000000)) (orderedInterval (-44901964720 / 1000000000000) (-44901957745 / 1000000000000), orderedInterval (15940737352 / 1000000000000) (15940744326 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_stateChecks8 :
    compactCertificate388.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (474809337851247 / 4000000000000)) (orderedInterval (7759761401 / 1000000000000) (7759761403 / 1000000000000), orderedInterval (72788973359 / 1000000000000) (72788973361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1930073597739087 / 4000000000000)) (orderedInterval (-17469349883 / 1000000000000) (-17469349336 / 1000000000000), orderedInterval (31864469257 / 1000000000000) (31864469804 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1289199715836033 / 4000000000000)) (orderedInterval (21272465032 / 1000000000000) (21272466435 / 1000000000000), orderedInterval (-39055093807 / 1000000000000) (-39055092403 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_states : ∀ j,
    BesselStateValid (compactCertificate388.point j) (compactCertificate388.state j) :=
  compactCertificate388.statesValid_of_checks3 compactCertificate388_stateChecks0
    compactCertificate388_stateChecks1 compactCertificate388_stateChecks2
    compactCertificate388_stateChecks3 compactCertificate388_stateChecks4
    compactCertificate388_stateChecks5 compactCertificate388_stateChecks6
    compactCertificate388_stateChecks7 compactCertificate388_stateChecks8

theorem compactCertificate388_chunkChecks0_0 :
    compactCertificate388.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (519 / 2) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22311121544 / 1000000000000) (22311122946 / 1000000000000), orderedInterval (-44263707345 / 1000000000000) (-44263705942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (764586101960619 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16730074408 / 1000000000000) (-16730074407 / 1000000000000), orderedInterval (-55188899282 / 1000000000000) (-55188899281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (247251435961227 / 800000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41759879977 / 1000000000000) (41759895016 / 1000000000000), orderedInterval (-17842251965 / 1000000000000) (-17842236926 / 1000000000000)))) (orderedInterval (11137973051 / 1000000000000) (11137974508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (223104317647233 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (1129110643 / 1000000000000) (1129110651 / 1000000000000), orderedInterval (106821675861 / 1000000000000) (106821675869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (599289579418701 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12278112965 / 1000000000000) (-12278112885 / 1000000000000), orderedInterval (64059979235 / 1000000000000) (64059979315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1627187786547417 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29058572963 / 1000000000000) (-29058546737 / 1000000000000), orderedInterval (26878897284 / 1000000000000) (26878923510 / 1000000000000)))) (orderedInterval (1605216248 / 1000000000000) (1605218147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1198579158837921 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42315648160 / 1000000000000) (-42315633049 / 1000000000000), orderedInterval (18345338236 / 1000000000000) (18345353347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2053785817796133 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29430294362 / 1000000000000) (-29430224104 / 1000000000000), orderedInterval (19361360325 / 1000000000000) (19361430583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1512809337851247 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37369612958 / 1000000000000) (37369639010 / 1000000000000), orderedInterval (-16984242725 / 1000000000000) (-16984216674 / 1000000000000)))) (orderedInterval (1810895669 / 1000000000000) (1810898481 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks0_1 :
    compactCertificate388.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2321038560644481 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4943868958 / 1000000000000) (4943868960 / 1000000000000), orderedInterval (-32756171597 / 1000000000000) (-32756171595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1340052237787449 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15043023792 / 1000000000000) (15043024001 / 1000000000000), orderedInterval (-40936904816 / 1000000000000) (-40936904608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2377946211624141 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32665177319 / 1000000000000) (-32665176866 / 1000000000000), orderedInterval (-1936991564 / 1000000000000) (-1936991111 / 1000000000000)))) (orderedInterval (-4407449019 / 1000000000000) (-4407448835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2221785809968929 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5718471285 / 1000000000000) (-5718471284 / 1000000000000), orderedInterval (-33363103743 / 1000000000000) (-33363103742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1585571190454257 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38986940602 / 1000000000000) (38986940611 / 1000000000000), orderedInterval (9227134916 / 1000000000000) (9227134925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1797868738256103 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31760985224 / 1000000000000) (-31760985223 / 1000000000000), orderedInterval (-20154445406 / 1000000000000) (-20154445405 / 1000000000000)))) (orderedInterval (3950681758 / 1000000000000) (3950681790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1498875516719607 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41073989878 / 1000000000000) (-41073989201 / 1000000000000), orderedInterval (3497512302 / 1000000000000) (3497512978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1324301975355747 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994939800 / 1000000000000) (-39994919536 / 1000000000000), orderedInterval (18040605823 / 1000000000000) (18040626087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (383834329606953 / 800000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3115226735 / 1000000000000) (3115226737 / 1000000000000), orderedInterval (-36295941530 / 1000000000000) (-36295941528 / 1000000000000)))) (orderedInterval (1894229558 / 1000000000000) (1894230751 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks0_2 :
    compactCertificate388.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1061705955786891 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35939279220 / 1000000000000) (35939328806 / 1000000000000), orderedInterval (-33337000523 / 1000000000000) (-33336950938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (900019896792051 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20951382072 / 1000000000000) (-20951381248 / 1000000000000), orderedInterval (48938305573 / 1000000000000) (48938306396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (563190662148753 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14050580623 / 1000000000000) (-14050580622 / 1000000000000), orderedInterval (-65708217209 / 1000000000000) (-65708217208 / 1000000000000)))) (orderedInterval (-5018000283 / 1000000000000) (-5017992242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (302885811191151 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (82003705769 / 1000000000000) (82003705770 / 1000000000000), orderedInterval (40478928362 / 1000000000000) (40478928363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (822393897066453 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45643277986 / 1000000000000) (-45643216298 / 1000000000000), orderedInterval (31940410035 / 1000000000000) (31940471722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1122908557827381 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44901964720 / 1000000000000) (-44901957745 / 1000000000000), orderedInterval (15940737352 / 1000000000000) (15940744326 / 1000000000000)))) (orderedInterval (2962528614 / 1000000000000) (2962530580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (474809337851247 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7759761401 / 1000000000000) (7759761403 / 1000000000000), orderedInterval (72788973359 / 1000000000000) (72788973361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1930073597739087 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17469349883 / 1000000000000) (-17469349336 / 1000000000000), orderedInterval (31864469257 / 1000000000000) (31864469804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1289199715836033 / 4000000000000) 0 (IntervalRat.scale (519 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21272465032 / 1000000000000) (21272466435 / 1000000000000), orderedInterval (-39055093807 / 1000000000000) (-39055092403 / 1000000000000)))) (orderedInterval (-2522464568 / 1000000000000) (-2522464188 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks0 :
    compactCertificate388.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate388.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate388_chunkChecks0_0
    compactCertificate388_chunkChecks0_1 compactCertificate388_chunkChecks0_2

theorem compactCertificate388_chunkChecks1_0 :
    compactCertificate388.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (519 / 2) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22311121544 / 1000000000000) (22311122946 / 1000000000000), orderedInterval (-44263707345 / 1000000000000) (-44263705942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (764586101960619 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16730074408 / 1000000000000) (-16730074407 / 1000000000000), orderedInterval (-55188899282 / 1000000000000) (-55188899281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (247251435961227 / 800000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41759879977 / 1000000000000) (41759895016 / 1000000000000), orderedInterval (-17842251965 / 1000000000000) (-17842236926 / 1000000000000)))) (orderedInterval (-19170361407 / 1000000000000) (-19170359778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (223104317647233 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (1129110643 / 1000000000000) (1129110651 / 1000000000000), orderedInterval (106821675861 / 1000000000000) (106821675869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (599289579418701 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12278112965 / 1000000000000) (-12278112885 / 1000000000000), orderedInterval (64059979235 / 1000000000000) (64059979315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1627187786547417 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29058572963 / 1000000000000) (-29058546737 / 1000000000000), orderedInterval (26878897284 / 1000000000000) (26878923510 / 1000000000000)))) (orderedInterval (-1894135495 / 1000000000000) (-1894132535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1198579158837921 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42315648160 / 1000000000000) (-42315633049 / 1000000000000), orderedInterval (18345338236 / 1000000000000) (18345353347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2053785817796133 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29430294362 / 1000000000000) (-29430224104 / 1000000000000), orderedInterval (19361360325 / 1000000000000) (19361430583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1512809337851247 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37369612958 / 1000000000000) (37369639010 / 1000000000000), orderedInterval (-16984242725 / 1000000000000) (-16984216674 / 1000000000000)))) (orderedInterval (-1779825999 / 1000000000000) (-1779820768 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks1_1 :
    compactCertificate388.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2321038560644481 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4943868958 / 1000000000000) (4943868960 / 1000000000000), orderedInterval (-32756171597 / 1000000000000) (-32756171595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1340052237787449 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15043023792 / 1000000000000) (15043024001 / 1000000000000), orderedInterval (-40936904816 / 1000000000000) (-40936904608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2377946211624141 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32665177319 / 1000000000000) (-32665176866 / 1000000000000), orderedInterval (-1936991564 / 1000000000000) (-1936991111 / 1000000000000)))) (orderedInterval (8468249127 / 1000000000000) (8468249509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2221785809968929 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5718471285 / 1000000000000) (-5718471284 / 1000000000000), orderedInterval (-33363103743 / 1000000000000) (-33363103742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1585571190454257 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38986940602 / 1000000000000) (38986940611 / 1000000000000), orderedInterval (9227134916 / 1000000000000) (9227134925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1797868738256103 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31760985224 / 1000000000000) (-31760985223 / 1000000000000), orderedInterval (-20154445406 / 1000000000000) (-20154445405 / 1000000000000)))) (orderedInterval (2798697908 / 1000000000000) (2798697960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1498875516719607 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41073989878 / 1000000000000) (-41073989201 / 1000000000000), orderedInterval (3497512302 / 1000000000000) (3497512978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1324301975355747 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994939800 / 1000000000000) (-39994919536 / 1000000000000), orderedInterval (18040605823 / 1000000000000) (18040626087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (383834329606953 / 800000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3115226735 / 1000000000000) (3115226737 / 1000000000000), orderedInterval (-36295941530 / 1000000000000) (-36295941528 / 1000000000000)))) (orderedInterval (-2977074114 / 1000000000000) (-2977072586 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks1_2 :
    compactCertificate388.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1061705955786891 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35939279220 / 1000000000000) (35939328806 / 1000000000000), orderedInterval (-33337000523 / 1000000000000) (-33336950938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (900019896792051 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20951382072 / 1000000000000) (-20951381248 / 1000000000000), orderedInterval (48938305573 / 1000000000000) (48938306396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (563190662148753 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14050580623 / 1000000000000) (-14050580622 / 1000000000000), orderedInterval (-65708217209 / 1000000000000) (-65708217208 / 1000000000000)))) (orderedInterval (1889711187 / 1000000000000) (1889719398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (302885811191151 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (82003705769 / 1000000000000) (82003705770 / 1000000000000), orderedInterval (40478928362 / 1000000000000) (40478928363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (822393897066453 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45643277986 / 1000000000000) (-45643216298 / 1000000000000), orderedInterval (31940410035 / 1000000000000) (31940471722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1122908557827381 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44901964720 / 1000000000000) (-44901957745 / 1000000000000), orderedInterval (15940737352 / 1000000000000) (15940744326 / 1000000000000)))) (orderedInterval (-2113832002 / 1000000000000) (-2113830287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (474809337851247 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7759761401 / 1000000000000) (7759761403 / 1000000000000), orderedInterval (72788973359 / 1000000000000) (72788973361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1930073597739087 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17469349883 / 1000000000000) (-17469349336 / 1000000000000), orderedInterval (31864469257 / 1000000000000) (31864469804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1289199715836033 / 4000000000000) 1 (IntervalRat.scale (519 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21272465032 / 1000000000000) (21272466435 / 1000000000000), orderedInterval (-39055093807 / 1000000000000) (-39055092403 / 1000000000000)))) (orderedInterval (4478837107 / 1000000000000) (4478837619 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks1 :
    compactCertificate388.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate388.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate388_chunkChecks1_0
    compactCertificate388_chunkChecks1_1 compactCertificate388_chunkChecks1_2

theorem compactCertificate388_chunkChecks2_0 :
    compactCertificate388.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (519 / 2) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22311121544 / 1000000000000) (22311122946 / 1000000000000), orderedInterval (-44263707345 / 1000000000000) (-44263705942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (764586101960619 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16730074408 / 1000000000000) (-16730074407 / 1000000000000), orderedInterval (-55188899282 / 1000000000000) (-55188899281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (247251435961227 / 800000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41759879977 / 1000000000000) (41759895016 / 1000000000000), orderedInterval (-17842251965 / 1000000000000) (-17842236926 / 1000000000000)))) (orderedInterval (-12160900158 / 1000000000000) (-12160898320 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (223104317647233 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (1129110643 / 1000000000000) (1129110651 / 1000000000000), orderedInterval (106821675861 / 1000000000000) (106821675869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (599289579418701 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12278112965 / 1000000000000) (-12278112885 / 1000000000000), orderedInterval (64059979235 / 1000000000000) (64059979315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1627187786547417 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29058572963 / 1000000000000) (-29058546737 / 1000000000000), orderedInterval (26878897284 / 1000000000000) (26878923510 / 1000000000000)))) (orderedInterval (-4919166430 / 1000000000000) (-4919161786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1198579158837921 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42315648160 / 1000000000000) (-42315633049 / 1000000000000), orderedInterval (18345338236 / 1000000000000) (18345353347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2053785817796133 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29430294362 / 1000000000000) (-29430224104 / 1000000000000), orderedInterval (19361360325 / 1000000000000) (19361430583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1512809337851247 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37369612958 / 1000000000000) (37369639010 / 1000000000000), orderedInterval (-16984242725 / 1000000000000) (-16984216674 / 1000000000000)))) (orderedInterval (-5465218802 / 1000000000000) (-5465208915 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks2_1 :
    compactCertificate388.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2321038560644481 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4943868958 / 1000000000000) (4943868960 / 1000000000000), orderedInterval (-32756171597 / 1000000000000) (-32756171595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1340052237787449 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15043023792 / 1000000000000) (15043024001 / 1000000000000), orderedInterval (-40936904816 / 1000000000000) (-40936904608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2377946211624141 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32665177319 / 1000000000000) (-32665176866 / 1000000000000), orderedInterval (-1936991564 / 1000000000000) (-1936991111 / 1000000000000)))) (orderedInterval (26872296194 / 1000000000000) (26872297017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2221785809968929 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5718471285 / 1000000000000) (-5718471284 / 1000000000000), orderedInterval (-33363103743 / 1000000000000) (-33363103742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1585571190454257 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38986940602 / 1000000000000) (38986940611 / 1000000000000), orderedInterval (9227134916 / 1000000000000) (9227134925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1797868738256103 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31760985224 / 1000000000000) (-31760985223 / 1000000000000), orderedInterval (-20154445406 / 1000000000000) (-20154445405 / 1000000000000)))) (orderedInterval (-9568289075 / 1000000000000) (-9568288990 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1498875516719607 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41073989878 / 1000000000000) (-41073989201 / 1000000000000), orderedInterval (3497512302 / 1000000000000) (3497512978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1324301975355747 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994939800 / 1000000000000) (-39994919536 / 1000000000000), orderedInterval (18040605823 / 1000000000000) (18040626087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (383834329606953 / 800000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3115226735 / 1000000000000) (3115226737 / 1000000000000), orderedInterval (-36295941530 / 1000000000000) (-36295941528 / 1000000000000)))) (orderedInterval (-2997675531 / 1000000000000) (-2997673567 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks2_2 :
    compactCertificate388.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1061705955786891 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35939279220 / 1000000000000) (35939328806 / 1000000000000), orderedInterval (-33337000523 / 1000000000000) (-33336950938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (900019896792051 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20951382072 / 1000000000000) (-20951381248 / 1000000000000), orderedInterval (48938305573 / 1000000000000) (48938306396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (563190662148753 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14050580623 / 1000000000000) (-14050580622 / 1000000000000), orderedInterval (-65708217209 / 1000000000000) (-65708217208 / 1000000000000)))) (orderedInterval (5247731935 / 1000000000000) (5247740354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (302885811191151 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (82003705769 / 1000000000000) (82003705770 / 1000000000000), orderedInterval (40478928362 / 1000000000000) (40478928363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (822393897066453 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45643277986 / 1000000000000) (-45643216298 / 1000000000000), orderedInterval (31940410035 / 1000000000000) (31940471722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1122908557827381 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44901964720 / 1000000000000) (-44901957745 / 1000000000000), orderedInterval (15940737352 / 1000000000000) (15940744326 / 1000000000000)))) (orderedInterval (-4540179505 / 1000000000000) (-4540177966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (474809337851247 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7759761401 / 1000000000000) (7759761403 / 1000000000000), orderedInterval (72788973359 / 1000000000000) (72788973361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1930073597739087 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17469349883 / 1000000000000) (-17469349336 / 1000000000000), orderedInterval (31864469257 / 1000000000000) (31864469804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1289199715836033 / 4000000000000) 2 (IntervalRat.scale (519 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21272465032 / 1000000000000) (21272466435 / 1000000000000), orderedInterval (-39055093807 / 1000000000000) (-39055092403 / 1000000000000)))) (orderedInterval (1213204686 / 1000000000000) (1213205398 / 1000000000000))) = true
  rfl'

theorem compactCertificate388_chunkChecks2 :
    compactCertificate388.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate388.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate388_chunkChecks2_0
    compactCertificate388_chunkChecks2_1 compactCertificate388_chunkChecks2_2

theorem compactCertificate388_chunkChecks3_0 :
    compactCertificate388.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (519 / 2) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22311121544 / 1000000000000) (22311122946 / 1000000000000), orderedInterval (-44263707345 / 1000000000000) (-44263705942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (764586101960619 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16730074408 / 1000000000000) (-16730074407 / 1000000000000), orderedInterval (-55188899282 / 1000000000000) (-55188899281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (247251435961227 / 800000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41759879977 / 1000000000000) (41759895016 / 1000000000000), orderedInterval (-17842251965 / 1000000000000) (-17842236926 / 1000000000000)))) (orderedInterval (19565500872 / 1000000000000) (19565502954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (223104317647233 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (1129110643 / 1000000000000) (1129110651 / 1000000000000), orderedInterval (106821675861 / 1000000000000) (106821675869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (599289579418701 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12278112965 / 1000000000000) (-12278112885 / 1000000000000), orderedInterval (64059979235 / 1000000000000) (64059979315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1627187786547417 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29058572963 / 1000000000000) (-29058546737 / 1000000000000), orderedInterval (26878897284 / 1000000000000) (26878923510 / 1000000000000)))) (orderedInterval (6941338920 / 1000000000000) (6941346195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1198579158837921 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42315648160 / 1000000000000) (-42315633049 / 1000000000000), orderedInterval (18345338236 / 1000000000000) (18345353347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2053785817796133 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29430294362 / 1000000000000) (-29430224104 / 1000000000000), orderedInterval (19361360325 / 1000000000000) (19361430583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1512809337851247 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37369612958 / 1000000000000) (37369639010 / 1000000000000), orderedInterval (-16984242725 / 1000000000000) (-16984216674 / 1000000000000)))) (orderedInterval (5917473076 / 1000000000000) (5917491931 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate388_chunkChecks3_1 :
    compactCertificate388.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2321038560644481 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4943868958 / 1000000000000) (4943868960 / 1000000000000), orderedInterval (-32756171597 / 1000000000000) (-32756171595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1340052237787449 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15043023792 / 1000000000000) (15043024001 / 1000000000000), orderedInterval (-40936904816 / 1000000000000) (-40936904608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2377946211624141 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32665177319 / 1000000000000) (-32665176866 / 1000000000000), orderedInterval (-1936991564 / 1000000000000) (-1936991111 / 1000000000000)))) (orderedInterval (-55340448749 / 1000000000000) (-55340446935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2221785809968929 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5718471285 / 1000000000000) (-5718471284 / 1000000000000), orderedInterval (-33363103743 / 1000000000000) (-33363103742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1585571190454257 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38986940602 / 1000000000000) (38986940611 / 1000000000000), orderedInterval (9227134916 / 1000000000000) (9227134925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1797868738256103 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31760985224 / 1000000000000) (-31760985223 / 1000000000000), orderedInterval (-20154445406 / 1000000000000) (-20154445405 / 1000000000000)))) (orderedInterval (-9509532803 / 1000000000000) (-9509532659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1498875516719607 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41073989878 / 1000000000000) (-41073989201 / 1000000000000), orderedInterval (3497512302 / 1000000000000) (3497512978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1324301975355747 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994939800 / 1000000000000) (-39994919536 / 1000000000000), orderedInterval (18040605823 / 1000000000000) (18040626087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (383834329606953 / 800000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3115226735 / 1000000000000) (3115226737 / 1000000000000), orderedInterval (-36295941530 / 1000000000000) (-36295941528 / 1000000000000)))) (orderedInterval (7907606506 / 1000000000000) (7907609029 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate388_chunkChecks3_2 :
    compactCertificate388.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1061705955786891 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35939279220 / 1000000000000) (35939328806 / 1000000000000), orderedInterval (-33337000523 / 1000000000000) (-33336950938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (900019896792051 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20951382072 / 1000000000000) (-20951381248 / 1000000000000), orderedInterval (48938305573 / 1000000000000) (48938306396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (563190662148753 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14050580623 / 1000000000000) (-14050580622 / 1000000000000), orderedInterval (-65708217209 / 1000000000000) (-65708217208 / 1000000000000)))) (orderedInterval (-3576828379 / 1000000000000) (-3576819777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (302885811191151 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (82003705769 / 1000000000000) (82003705770 / 1000000000000), orderedInterval (40478928362 / 1000000000000) (40478928363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (822393897066453 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45643277986 / 1000000000000) (-45643216298 / 1000000000000), orderedInterval (31940410035 / 1000000000000) (31940471722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1122908557827381 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44901964720 / 1000000000000) (-44901957745 / 1000000000000), orderedInterval (15940737352 / 1000000000000) (15940744326 / 1000000000000)))) (orderedInterval (1943089950 / 1000000000000) (1943091357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (474809337851247 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7759761401 / 1000000000000) (7759761403 / 1000000000000), orderedInterval (72788973359 / 1000000000000) (72788973361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1930073597739087 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17469349883 / 1000000000000) (-17469349336 / 1000000000000), orderedInterval (31864469257 / 1000000000000) (31864469804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1289199715836033 / 4000000000000) 3 (IntervalRat.scale (519 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21272465032 / 1000000000000) (21272466435 / 1000000000000), orderedInterval (-39055093807 / 1000000000000) (-39055092403 / 1000000000000)))) (orderedInterval (2589418855 / 1000000000000) (2589419878 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate388_chunkChecks3 :
    compactCertificate388.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate388.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate388_chunkChecks3_0
    compactCertificate388_chunkChecks3_1 compactCertificate388_chunkChecks3_2

theorem compactCertificate388_chunkChecks4_0 :
    compactCertificate388.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (519 / 2) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22311121544 / 1000000000000) (22311122946 / 1000000000000), orderedInterval (-44263707345 / 1000000000000) (-44263705942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (764586101960619 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16730074408 / 1000000000000) (-16730074407 / 1000000000000), orderedInterval (-55188899282 / 1000000000000) (-55188899281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (247251435961227 / 800000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41759879977 / 1000000000000) (41759895016 / 1000000000000), orderedInterval (-17842251965 / 1000000000000) (-17842236926 / 1000000000000)))) (orderedInterval (13577126244 / 1000000000000) (13577128624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (223104317647233 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (1129110643 / 1000000000000) (1129110651 / 1000000000000), orderedInterval (106821675861 / 1000000000000) (106821675869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (599289579418701 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12278112965 / 1000000000000) (-12278112885 / 1000000000000), orderedInterval (64059979235 / 1000000000000) (64059979315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1627187786547417 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29058572963 / 1000000000000) (-29058546737 / 1000000000000), orderedInterval (26878897284 / 1000000000000) (26878923510 / 1000000000000)))) (orderedInterval (12371619611 / 1000000000000) (12371631039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1198579158837921 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-42315648160 / 1000000000000) (-42315633049 / 1000000000000), orderedInterval (18345338236 / 1000000000000) (18345353347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2053785817796133 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29430294362 / 1000000000000) (-29430224104 / 1000000000000), orderedInterval (19361360325 / 1000000000000) (19361430583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1512809337851247 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (37369612958 / 1000000000000) (37369639010 / 1000000000000), orderedInterval (-16984242725 / 1000000000000) (-16984216674 / 1000000000000)))) (orderedInterval (17941309074 / 1000000000000) (17941345423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate388_chunkChecks4_1 :
    compactCertificate388.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2321038560644481 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4943868958 / 1000000000000) (4943868960 / 1000000000000), orderedInterval (-32756171597 / 1000000000000) (-32756171595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1340052237787449 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15043023792 / 1000000000000) (15043024001 / 1000000000000), orderedInterval (-40936904816 / 1000000000000) (-40936904608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2377946211624141 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32665177319 / 1000000000000) (-32665176866 / 1000000000000), orderedInterval (-1936991564 / 1000000000000) (-1936991111 / 1000000000000)))) (orderedInterval (-146338141110 / 1000000000000) (-146338137055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2221785809968929 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5718471285 / 1000000000000) (-5718471284 / 1000000000000), orderedInterval (-33363103743 / 1000000000000) (-33363103742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1585571190454257 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38986940602 / 1000000000000) (38986940611 / 1000000000000), orderedInterval (9227134916 / 1000000000000) (9227134925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1797868738256103 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31760985224 / 1000000000000) (-31760985223 / 1000000000000), orderedInterval (-20154445406 / 1000000000000) (-20154445405 / 1000000000000)))) (orderedInterval (23758792968 / 1000000000000) (23758793218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1498875516719607 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41073989878 / 1000000000000) (-41073989201 / 1000000000000), orderedInterval (3497512302 / 1000000000000) (3497512978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1324301975355747 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39994939800 / 1000000000000) (-39994919536 / 1000000000000), orderedInterval (18040605823 / 1000000000000) (18040626087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (383834329606953 / 800000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3115226735 / 1000000000000) (3115226737 / 1000000000000), orderedInterval (-36295941530 / 1000000000000) (-36295941528 / 1000000000000)))) (orderedInterval (4872934705 / 1000000000000) (4872937962 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate388_chunkChecks4_2 :
    compactCertificate388.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1061705955786891 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35939279220 / 1000000000000) (35939328806 / 1000000000000), orderedInterval (-33337000523 / 1000000000000) (-33336950938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (900019896792051 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20951382072 / 1000000000000) (-20951381248 / 1000000000000), orderedInterval (48938305573 / 1000000000000) (48938306396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (563190662148753 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14050580623 / 1000000000000) (-14050580622 / 1000000000000), orderedInterval (-65708217209 / 1000000000000) (-65708217208 / 1000000000000)))) (orderedInterval (-5631365380 / 1000000000000) (-5631356555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (302885811191151 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (82003705769 / 1000000000000) (82003705770 / 1000000000000), orderedInterval (40478928362 / 1000000000000) (40478928363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (822393897066453 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45643277986 / 1000000000000) (-45643216298 / 1000000000000), orderedInterval (31940410035 / 1000000000000) (31940471722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1122908557827381 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44901964720 / 1000000000000) (-44901957745 / 1000000000000), orderedInterval (15940737352 / 1000000000000) (15940744326 / 1000000000000)))) (orderedInterval (5095053830 / 1000000000000) (5095055155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (474809337851247 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7759761401 / 1000000000000) (7759761403 / 1000000000000), orderedInterval (72788973359 / 1000000000000) (72788973361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1930073597739087 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17469349883 / 1000000000000) (-17469349336 / 1000000000000), orderedInterval (31864469257 / 1000000000000) (31864469804 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1289199715836033 / 4000000000000) 4 (IntervalRat.scale (519 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21272465032 / 1000000000000) (21272466435 / 1000000000000), orderedInterval (-39055093807 / 1000000000000) (-39055092403 / 1000000000000)))) (orderedInterval (7483473998 / 1000000000000) (7483475532 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate388_chunkChecks4 :
    compactCertificate388.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate388.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate388_chunkChecks4_0
    compactCertificate388_chunkChecks4_1 compactCertificate388_chunkChecks4_2

theorem compactCertificate388_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate388.chunkCheck r b = true :=
  compactCertificate388.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate388_chunkChecks0
    · exact compactCertificate388_chunkChecks1
    · exact compactCertificate388_chunkChecks2
    · exact compactCertificate388_chunkChecks3
    · exact compactCertificate388_chunkChecks4)

theorem compactCertificate388_coefficient0 :
    compactCertificate388.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate388_coefficient1 :
    compactCertificate388.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate388_coefficient2 :
    compactCertificate388.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate388_coefficient3 :
    compactCertificate388.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate388_coefficient4 :
    compactCertificate388.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate388_coefficients : ∀ r : Fin 5,
    compactCertificate388.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate388_coefficient0
  · exact compactCertificate388_coefficient1
  · exact compactCertificate388_coefficient2
  · exact compactCertificate388_coefficient3
  · exact compactCertificate388_coefficient4

theorem compactCertificate388_lower : (1 : ℚ) ≤ compactCertificate388.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate388, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate388_proves {t : ℝ} (ht : t ∈ compactCertificate388.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate388.proves compactCertificate388_states compactCertificate388_chunks
    compactCertificate388_coefficients compactCertificate388_lower ht

end Erdos232
