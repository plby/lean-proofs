/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate438 : CompactCertificate where
  left := 309
  right := 310
  center := 619 / 2
  grid := fun i =>
    match i.val with
    | 0 => 99
    | 1 => 73
    | 2 => 117
    | 3 => 21
    | 4 => 57
    | 5 => 155
    | 6 => 114
    | 7 => 195
    | 8 => 144
    | 9 => 220
    | 10 => 127
    | 11 => 226
    | 12 => 211
    | 13 => 151
    | 14 => 171
    | 15 => 142
    | 16 => 126
    | 17 => 182
    | 18 => 101
    | 19 => 85
    | 20 => 53
    | 21 => 29
    | 22 => 78
    | 23 => 107
    | 24 => 45
    | 25 => 183
    | _ => 122
  point := fun i =>
    match i.val with
    | 0 => 619 / 2
    | 1 => 911905196750719 / 4000000000000
    | 2 => 294891404354527 / 800000000000
    | 3 => 266091662087933 / 4000000000000
    | 4 => 714759633256601 / 4000000000000
    | 5 => 1940711444841717 / 4000000000000
    | 6 => 1429519266513821 / 4000000000000
    | 7 => 2449505628546833 / 4000000000000
    | 8 => 1804294759402547 / 4000000000000
    | 9 => 2768252156144381 / 4000000000000
    | 10 => 1598251127534549 / 4000000000000
    | 11 => 2836124672438041 / 4000000000000
    | 12 => 2649875561408029 / 4000000000000
    | 13 => 1891076236784557 / 4000000000000
    | 14 => 2144278899769803 / 4000000000000
    | 15 => 1787676194314907 / 4000000000000
    | 16 => 1579466132457047 / 4000000000000
    | 17 => 457790847835653 / 800000000000
    | 18 => 1266273577325791 / 4000000000000
    | 19 => 1073434135094951 / 4000000000000
    | 20 => 671705240597453 / 4000000000000
    | 21 => 361245312384051 / 4000000000000
    | 22 => 980851295345153 / 4000000000000
    | 23 => 1339268588237281 / 4000000000000
    | 24 => 566294759402547 / 4000000000000
    | 25 => 2301956757226387 / 4000000000000
    | _ => 1537600431796733 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (30335180068 / 1000000000000) (30335197557 / 1000000000000), orderedInterval (-33764091619 / 1000000000000) (-33764074130 / 1000000000000))
    | 1 => (orderedInterval (28743421488 / 1000000000000) (28743426960 / 1000000000000), orderedInterval (-44406030498 / 1000000000000) (-44406025026 / 1000000000000))
    | 2 => (orderedInterval (-40137798187 / 1000000000000) (-40137793231 / 1000000000000), orderedInterval (10825618015 / 1000000000000) (10825622971 / 1000000000000))
    | 3 => (orderedInterval (-95071556330 / 1000000000000) (-95071556329 / 1000000000000), orderedInterval (-22330871675 / 1000000000000) (-22330871674 / 1000000000000))
    | 4 => (orderedInterval (-23453871379 / 1000000000000) (-23453871378 / 1000000000000), orderedInterval (-54821826013 / 1000000000000) (-54821826012 / 1000000000000))
    | 5 => (orderedInterval (30161067785 / 1000000000000) (30161143409 / 1000000000000), orderedInterval (-20092133173 / 1000000000000) (-20092057549 / 1000000000000))
    | 6 => (orderedInterval (983418445 / 1000000000000) (983418447 / 1000000000000), orderedInterval (42193269384 / 1000000000000) (42193269386 / 1000000000000))
    | 7 => (orderedInterval (-16881228473 / 1000000000000) (-16881228472 / 1000000000000), orderedInterval (-27456441873 / 1000000000000) (-27456441872 / 1000000000000))
    | 8 => (orderedInterval (-19009010270 / 1000000000000) (-19009009327 / 1000000000000), orderedInterval (32424791443 / 1000000000000) (32424792387 / 1000000000000))
    | 9 => (orderedInterval (30085072509 / 1000000000000) (30085079196 / 1000000000000), orderedInterval (-3865557985 / 1000000000000) (-3865551298 / 1000000000000))
    | 10 => (orderedInterval (-39078636572 / 1000000000000) (-39078636558 / 1000000000000), orderedInterval (-8084362775 / 1000000000000) (-8084362761 / 1000000000000))
    | 11 => (orderedInterval (-5469149081 / 1000000000000) (-5469149079 / 1000000000000), orderedInterval (29465041024 / 1000000000000) (29465041026 / 1000000000000))
    | 12 => (orderedInterval (-11442255706 / 1000000000000) (-11442255705 / 1000000000000), orderedInterval (-28802049707 / 1000000000000) (-28802049706 / 1000000000000))
    | 13 => (orderedInterval (26987040940 / 1000000000000) (26987060350 / 1000000000000), orderedInterval (-24893700520 / 1000000000000) (-24893681111 / 1000000000000))
    | 14 => (orderedInterval (12057604622 / 1000000000000) (12057604676 / 1000000000000), orderedInterval (-32294113797 / 1000000000000) (-32294113743 / 1000000000000))
    | 15 => (orderedInterval (37728075387 / 1000000000000) (37728075916 / 1000000000000), orderedInterval (-1069192050 / 1000000000000) (-1069191520 / 1000000000000))
    | 16 => (orderedInterval (-7546112034 / 1000000000000) (-7546112022 / 1000000000000), orderedInterval (39446819123 / 1000000000000) (39446819135 / 1000000000000))
    | 17 => (orderedInterval (31693220928 / 1000000000000) (31693220937 / 1000000000000), orderedInterval (10366875967 / 1000000000000) (10366875977 / 1000000000000))
    | 18 => (orderedInterval (-2355012185 / 1000000000000) (-2355012184 / 1000000000000), orderedInterval (-44778628750 / 1000000000000) (-44778628749 / 1000000000000))
    | 19 => (orderedInterval (-41843135973 / 1000000000000) (-41843092555 / 1000000000000), orderedInterval (25006336363 / 1000000000000) (25006379782 / 1000000000000))
    | 20 => (orderedInterval (-49541841305 / 1000000000000) (-49541775290 / 1000000000000), orderedInterval (36707978357 / 1000000000000) (36708044372 / 1000000000000))
    | 21 => (orderedInterval (910489500 / 1000000000000) (910489508 / 1000000000000), orderedInterval (-83960073488 / 1000000000000) (-83960073479 / 1000000000000))
    | 22 => (orderedInterval (41548839905 / 1000000000000) (41548839906 / 1000000000000), orderedInterval (29409092307 / 1000000000000) (29409092308 / 1000000000000))
    | 23 => (orderedInterval (22726372949 / 1000000000000) (22726375234 / 1000000000000), orderedInterval (-37248295016 / 1000000000000) (-37248292732 / 1000000000000))
    | 24 => (orderedInterval (-55934020447 / 1000000000000) (-55934020446 / 1000000000000), orderedInterval (-36790460013 / 1000000000000) (-36790460012 / 1000000000000))
    | 25 => (orderedInterval (-32543858722 / 1000000000000) (-32543858669 / 1000000000000), orderedInterval (-6836167200 / 1000000000000) (-6836167147 / 1000000000000))
    | _ => (orderedInterval (38364922345 / 1000000000000) (38364934222 / 1000000000000), orderedInterval (-13624500307 / 1000000000000) (-13624488430 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9936304596 / 1000000000000) (9936311891 / 1000000000000)
      | 1 => orderedInterval (-1969027690 / 1000000000000) (-1969022276 / 1000000000000)
      | 2 => orderedInterval (61274345 / 1000000000000) (61274386 / 1000000000000)
      | 3 => orderedInterval (-9018632545 / 1000000000000) (-9018631233 / 1000000000000)
      | 4 => orderedInterval (2697521519 / 1000000000000) (2697523392 / 1000000000000)
      | 5 => orderedInterval (1678981908 / 1000000000000) (1678981946 / 1000000000000)
      | 6 => orderedInterval (1132017738 / 1000000000000) (1132022423 / 1000000000000)
      | 7 => orderedInterval (-2701148828 / 1000000000000) (-2701148616 / 1000000000000)
      | _ => orderedInterval (-4886340105 / 1000000000000) (-4886337786 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12931097305 / 1000000000000) (-12931089964 / 1000000000000)
      | 1 => orderedInterval (1135513309 / 1000000000000) (1135521779 / 1000000000000)
      | 2 => orderedInterval (2817712174 / 1000000000000) (2817712239 / 1000000000000)
      | 3 => orderedInterval (10358281914 / 1000000000000) (10358284827 / 1000000000000)
      | 4 => orderedInterval (-2199800594 / 1000000000000) (-2199797730 / 1000000000000)
      | 5 => orderedInterval (-2407117282 / 1000000000000) (-2407117228 / 1000000000000)
      | 6 => orderedInterval (6744457178 / 1000000000000) (6744460547 / 1000000000000)
      | 7 => orderedInterval (3011948532 / 1000000000000) (3011948755 / 1000000000000)
      | _ => orderedInterval (4108222973 / 1000000000000) (4108225870 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8786360216 / 1000000000000) (-8786352792 / 1000000000000)
      | 1 => orderedInterval (5503193698 / 1000000000000) (5503206995 / 1000000000000)
      | 2 => orderedInterval (-1071678063 / 1000000000000) (-1071677960 / 1000000000000)
      | 3 => orderedInterval (35601295906 / 1000000000000) (35601302404 / 1000000000000)
      | 4 => orderedInterval (-6710838384 / 1000000000000) (-6710833991 / 1000000000000)
      | 5 => orderedInterval (-4377572054 / 1000000000000) (-4377571975 / 1000000000000)
      | 6 => orderedInterval (-1721469877 / 1000000000000) (-1721467317 / 1000000000000)
      | 7 => orderedInterval (2621719854 / 1000000000000) (2621720093 / 1000000000000)
      | _ => orderedInterval (2001979825 / 1000000000000) (2001983464 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12503307185 / 1000000000000) (12503314686 / 1000000000000)
      | 1 => orderedInterval (-5137373844 / 1000000000000) (-5137353004 / 1000000000000)
      | 2 => orderedInterval (-8982207857 / 1000000000000) (-8982207688 / 1000000000000)
      | 3 => orderedInterval (-56865497237 / 1000000000000) (-56865482734 / 1000000000000)
      | 4 => orderedInterval (2463668642 / 1000000000000) (2463675367 / 1000000000000)
      | 5 => orderedInterval (3061545832 / 1000000000000) (3061545952 / 1000000000000)
      | 6 => orderedInterval (-6924209020 / 1000000000000) (-6924207000 / 1000000000000)
      | 7 => orderedInterval (-3329207482 / 1000000000000) (-3329207225 / 1000000000000)
      | _ => orderedInterval (-8460269757 / 1000000000000) (-8460265174 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (7282638351 / 1000000000000) (7282645969 / 1000000000000)
      | 1 => orderedInterval (-13008071883 / 1000000000000) (-13008039149 / 1000000000000)
      | 2 => orderedInterval (5965332578 / 1000000000000) (5965332862 / 1000000000000)
      | 3 => orderedInterval (-162733111390 / 1000000000000) (-162733078937 / 1000000000000)
      | 4 => orderedInterval (17664844901 / 1000000000000) (17664855231 / 1000000000000)
      | 5 => orderedInterval (12501397430 / 1000000000000) (12501397617 / 1000000000000)
      | 6 => orderedInterval (1655721042 / 1000000000000) (1655722696 / 1000000000000)
      | 7 => orderedInterval (-2735433669 / 1000000000000) (-2735433391 / 1000000000000)
      | _ => orderedInterval (14578549981 / 1000000000000) (14578555804 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3069049062 / 1000000000000) (-3069025873 / 1000000000000)
    | 1 => orderedInterval (10638120899 / 1000000000000) (10638149095 / 1000000000000)
    | 2 => orderedInterval (23060270689 / 1000000000000) (23060308921 / 1000000000000)
    | 3 => orderedInterval (-71670243538 / 1000000000000) (-71670186820 / 1000000000000)
    | _ => orderedInterval (-118828132659 / 1000000000000) (-118828041298 / 1000000000000)

theorem compactCertificate438_stateChecks0 :
    compactCertificate438.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (619 / 2)) (orderedInterval (30335180068 / 1000000000000) (30335197557 / 1000000000000), orderedInterval (-33764091619 / 1000000000000) (-33764074130 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (911905196750719 / 4000000000000)) (orderedInterval (28743421488 / 1000000000000) (28743426960 / 1000000000000), orderedInterval (-44406030498 / 1000000000000) (-44406025026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (294891404354527 / 800000000000)) (orderedInterval (-40137798187 / 1000000000000) (-40137793231 / 1000000000000), orderedInterval (10825618015 / 1000000000000) (10825622971 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks1 :
    compactCertificate438.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (266091662087933 / 4000000000000)) (orderedInterval (-95071556330 / 1000000000000) (-95071556329 / 1000000000000), orderedInterval (-22330871675 / 1000000000000) (-22330871674 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (714759633256601 / 4000000000000)) (orderedInterval (-23453871379 / 1000000000000) (-23453871378 / 1000000000000), orderedInterval (-54821826013 / 1000000000000) (-54821826012 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1940711444841717 / 4000000000000)) (orderedInterval (30161067785 / 1000000000000) (30161143409 / 1000000000000), orderedInterval (-20092133173 / 1000000000000) (-20092057549 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks2 :
    compactCertificate438.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1429519266513821 / 4000000000000)) (orderedInterval (983418445 / 1000000000000) (983418447 / 1000000000000), orderedInterval (42193269384 / 1000000000000) (42193269386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2449505628546833 / 4000000000000)) (orderedInterval (-16881228473 / 1000000000000) (-16881228472 / 1000000000000), orderedInterval (-27456441873 / 1000000000000) (-27456441872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1804294759402547 / 4000000000000)) (orderedInterval (-19009010270 / 1000000000000) (-19009009327 / 1000000000000), orderedInterval (32424791443 / 1000000000000) (32424792387 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks3 :
    compactCertificate438.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2768252156144381 / 4000000000000)) (orderedInterval (30085072509 / 1000000000000) (30085079196 / 1000000000000), orderedInterval (-3865557985 / 1000000000000) (-3865551298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1598251127534549 / 4000000000000)) (orderedInterval (-39078636572 / 1000000000000) (-39078636558 / 1000000000000), orderedInterval (-8084362775 / 1000000000000) (-8084362761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2836124672438041 / 4000000000000)) (orderedInterval (-5469149081 / 1000000000000) (-5469149079 / 1000000000000), orderedInterval (29465041024 / 1000000000000) (29465041026 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks4 :
    compactCertificate438.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2649875561408029 / 4000000000000)) (orderedInterval (-11442255706 / 1000000000000) (-11442255705 / 1000000000000), orderedInterval (-28802049707 / 1000000000000) (-28802049706 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1891076236784557 / 4000000000000)) (orderedInterval (26987040940 / 1000000000000) (26987060350 / 1000000000000), orderedInterval (-24893700520 / 1000000000000) (-24893681111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2144278899769803 / 4000000000000)) (orderedInterval (12057604622 / 1000000000000) (12057604676 / 1000000000000), orderedInterval (-32294113797 / 1000000000000) (-32294113743 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks5 :
    compactCertificate438.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1787676194314907 / 4000000000000)) (orderedInterval (37728075387 / 1000000000000) (37728075916 / 1000000000000), orderedInterval (-1069192050 / 1000000000000) (-1069191520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1579466132457047 / 4000000000000)) (orderedInterval (-7546112034 / 1000000000000) (-7546112022 / 1000000000000), orderedInterval (39446819123 / 1000000000000) (39446819135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (457790847835653 / 800000000000)) (orderedInterval (31693220928 / 1000000000000) (31693220937 / 1000000000000), orderedInterval (10366875967 / 1000000000000) (10366875977 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks6 :
    compactCertificate438.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1266273577325791 / 4000000000000)) (orderedInterval (-2355012185 / 1000000000000) (-2355012184 / 1000000000000), orderedInterval (-44778628750 / 1000000000000) (-44778628749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1073434135094951 / 4000000000000)) (orderedInterval (-41843135973 / 1000000000000) (-41843092555 / 1000000000000), orderedInterval (25006336363 / 1000000000000) (25006379782 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (671705240597453 / 4000000000000)) (orderedInterval (-49541841305 / 1000000000000) (-49541775290 / 1000000000000), orderedInterval (36707978357 / 1000000000000) (36708044372 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks7 :
    compactCertificate438.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (361245312384051 / 4000000000000)) (orderedInterval (910489500 / 1000000000000) (910489508 / 1000000000000), orderedInterval (-83960073488 / 1000000000000) (-83960073479 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (980851295345153 / 4000000000000)) (orderedInterval (41548839905 / 1000000000000) (41548839906 / 1000000000000), orderedInterval (29409092307 / 1000000000000) (29409092308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1339268588237281 / 4000000000000)) (orderedInterval (22726372949 / 1000000000000) (22726375234 / 1000000000000), orderedInterval (-37248295016 / 1000000000000) (-37248292732 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_stateChecks8 :
    compactCertificate438.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (566294759402547 / 4000000000000)) (orderedInterval (-55934020447 / 1000000000000) (-55934020446 / 1000000000000), orderedInterval (-36790460013 / 1000000000000) (-36790460012 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2301956757226387 / 4000000000000)) (orderedInterval (-32543858722 / 1000000000000) (-32543858669 / 1000000000000), orderedInterval (-6836167200 / 1000000000000) (-6836167147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1537600431796733 / 4000000000000)) (orderedInterval (38364922345 / 1000000000000) (38364934222 / 1000000000000), orderedInterval (-13624500307 / 1000000000000) (-13624488430 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_states : ∀ j,
    BesselStateValid (compactCertificate438.point j) (compactCertificate438.state j) :=
  compactCertificate438.statesValid_of_checks3 compactCertificate438_stateChecks0
    compactCertificate438_stateChecks1 compactCertificate438_stateChecks2
    compactCertificate438_stateChecks3 compactCertificate438_stateChecks4
    compactCertificate438_stateChecks5 compactCertificate438_stateChecks6
    compactCertificate438_stateChecks7 compactCertificate438_stateChecks8

theorem compactCertificate438_chunkChecks0_0 :
    compactCertificate438.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (619 / 2) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30335180068 / 1000000000000) (30335197557 / 1000000000000), orderedInterval (-33764091619 / 1000000000000) (-33764074130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (911905196750719 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28743421488 / 1000000000000) (28743426960 / 1000000000000), orderedInterval (-44406030498 / 1000000000000) (-44406025026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (294891404354527 / 800000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40137798187 / 1000000000000) (-40137793231 / 1000000000000), orderedInterval (10825618015 / 1000000000000) (10825622971 / 1000000000000)))) (orderedInterval (9936304596 / 1000000000000) (9936311891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (266091662087933 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95071556330 / 1000000000000) (-95071556329 / 1000000000000), orderedInterval (-22330871675 / 1000000000000) (-22330871674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (714759633256601 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23453871379 / 1000000000000) (-23453871378 / 1000000000000), orderedInterval (-54821826013 / 1000000000000) (-54821826012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1940711444841717 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30161067785 / 1000000000000) (30161143409 / 1000000000000), orderedInterval (-20092133173 / 1000000000000) (-20092057549 / 1000000000000)))) (orderedInterval (-1969027690 / 1000000000000) (-1969022276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1429519266513821 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (983418445 / 1000000000000) (983418447 / 1000000000000), orderedInterval (42193269384 / 1000000000000) (42193269386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2449505628546833 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16881228473 / 1000000000000) (-16881228472 / 1000000000000), orderedInterval (-27456441873 / 1000000000000) (-27456441872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1804294759402547 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19009010270 / 1000000000000) (-19009009327 / 1000000000000), orderedInterval (32424791443 / 1000000000000) (32424792387 / 1000000000000)))) (orderedInterval (61274345 / 1000000000000) (61274386 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks0_1 :
    compactCertificate438.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2768252156144381 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30085072509 / 1000000000000) (30085079196 / 1000000000000), orderedInterval (-3865557985 / 1000000000000) (-3865551298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1598251127534549 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39078636572 / 1000000000000) (-39078636558 / 1000000000000), orderedInterval (-8084362775 / 1000000000000) (-8084362761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2836124672438041 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5469149081 / 1000000000000) (-5469149079 / 1000000000000), orderedInterval (29465041024 / 1000000000000) (29465041026 / 1000000000000)))) (orderedInterval (-9018632545 / 1000000000000) (-9018631233 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2649875561408029 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11442255706 / 1000000000000) (-11442255705 / 1000000000000), orderedInterval (-28802049707 / 1000000000000) (-28802049706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1891076236784557 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26987040940 / 1000000000000) (26987060350 / 1000000000000), orderedInterval (-24893700520 / 1000000000000) (-24893681111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2144278899769803 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12057604622 / 1000000000000) (12057604676 / 1000000000000), orderedInterval (-32294113797 / 1000000000000) (-32294113743 / 1000000000000)))) (orderedInterval (2697521519 / 1000000000000) (2697523392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1787676194314907 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37728075387 / 1000000000000) (37728075916 / 1000000000000), orderedInterval (-1069192050 / 1000000000000) (-1069191520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1579466132457047 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7546112034 / 1000000000000) (-7546112022 / 1000000000000), orderedInterval (39446819123 / 1000000000000) (39446819135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (457790847835653 / 800000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31693220928 / 1000000000000) (31693220937 / 1000000000000), orderedInterval (10366875967 / 1000000000000) (10366875977 / 1000000000000)))) (orderedInterval (1678981908 / 1000000000000) (1678981946 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks0_2 :
    compactCertificate438.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1266273577325791 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2355012185 / 1000000000000) (-2355012184 / 1000000000000), orderedInterval (-44778628750 / 1000000000000) (-44778628749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1073434135094951 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41843135973 / 1000000000000) (-41843092555 / 1000000000000), orderedInterval (25006336363 / 1000000000000) (25006379782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (671705240597453 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49541841305 / 1000000000000) (-49541775290 / 1000000000000), orderedInterval (36707978357 / 1000000000000) (36708044372 / 1000000000000)))) (orderedInterval (1132017738 / 1000000000000) (1132022423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (361245312384051 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (910489500 / 1000000000000) (910489508 / 1000000000000), orderedInterval (-83960073488 / 1000000000000) (-83960073479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (980851295345153 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41548839905 / 1000000000000) (41548839906 / 1000000000000), orderedInterval (29409092307 / 1000000000000) (29409092308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1339268588237281 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22726372949 / 1000000000000) (22726375234 / 1000000000000), orderedInterval (-37248295016 / 1000000000000) (-37248292732 / 1000000000000)))) (orderedInterval (-2701148828 / 1000000000000) (-2701148616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (566294759402547 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-55934020447 / 1000000000000) (-55934020446 / 1000000000000), orderedInterval (-36790460013 / 1000000000000) (-36790460012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2301956757226387 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32543858722 / 1000000000000) (-32543858669 / 1000000000000), orderedInterval (-6836167200 / 1000000000000) (-6836167147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1537600431796733 / 4000000000000) 0 (IntervalRat.scale (619 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38364922345 / 1000000000000) (38364934222 / 1000000000000), orderedInterval (-13624500307 / 1000000000000) (-13624488430 / 1000000000000)))) (orderedInterval (-4886340105 / 1000000000000) (-4886337786 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks0 :
    compactCertificate438.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate438.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate438_chunkChecks0_0
    compactCertificate438_chunkChecks0_1 compactCertificate438_chunkChecks0_2

theorem compactCertificate438_chunkChecks1_0 :
    compactCertificate438.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (619 / 2) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30335180068 / 1000000000000) (30335197557 / 1000000000000), orderedInterval (-33764091619 / 1000000000000) (-33764074130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (911905196750719 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28743421488 / 1000000000000) (28743426960 / 1000000000000), orderedInterval (-44406030498 / 1000000000000) (-44406025026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (294891404354527 / 800000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40137798187 / 1000000000000) (-40137793231 / 1000000000000), orderedInterval (10825618015 / 1000000000000) (10825622971 / 1000000000000)))) (orderedInterval (-12931097305 / 1000000000000) (-12931089964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (266091662087933 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95071556330 / 1000000000000) (-95071556329 / 1000000000000), orderedInterval (-22330871675 / 1000000000000) (-22330871674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (714759633256601 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23453871379 / 1000000000000) (-23453871378 / 1000000000000), orderedInterval (-54821826013 / 1000000000000) (-54821826012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1940711444841717 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30161067785 / 1000000000000) (30161143409 / 1000000000000), orderedInterval (-20092133173 / 1000000000000) (-20092057549 / 1000000000000)))) (orderedInterval (1135513309 / 1000000000000) (1135521779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1429519266513821 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (983418445 / 1000000000000) (983418447 / 1000000000000), orderedInterval (42193269384 / 1000000000000) (42193269386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2449505628546833 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16881228473 / 1000000000000) (-16881228472 / 1000000000000), orderedInterval (-27456441873 / 1000000000000) (-27456441872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1804294759402547 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19009010270 / 1000000000000) (-19009009327 / 1000000000000), orderedInterval (32424791443 / 1000000000000) (32424792387 / 1000000000000)))) (orderedInterval (2817712174 / 1000000000000) (2817712239 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks1_1 :
    compactCertificate438.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2768252156144381 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30085072509 / 1000000000000) (30085079196 / 1000000000000), orderedInterval (-3865557985 / 1000000000000) (-3865551298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1598251127534549 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39078636572 / 1000000000000) (-39078636558 / 1000000000000), orderedInterval (-8084362775 / 1000000000000) (-8084362761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2836124672438041 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5469149081 / 1000000000000) (-5469149079 / 1000000000000), orderedInterval (29465041024 / 1000000000000) (29465041026 / 1000000000000)))) (orderedInterval (10358281914 / 1000000000000) (10358284827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2649875561408029 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11442255706 / 1000000000000) (-11442255705 / 1000000000000), orderedInterval (-28802049707 / 1000000000000) (-28802049706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1891076236784557 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26987040940 / 1000000000000) (26987060350 / 1000000000000), orderedInterval (-24893700520 / 1000000000000) (-24893681111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2144278899769803 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12057604622 / 1000000000000) (12057604676 / 1000000000000), orderedInterval (-32294113797 / 1000000000000) (-32294113743 / 1000000000000)))) (orderedInterval (-2199800594 / 1000000000000) (-2199797730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1787676194314907 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37728075387 / 1000000000000) (37728075916 / 1000000000000), orderedInterval (-1069192050 / 1000000000000) (-1069191520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1579466132457047 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7546112034 / 1000000000000) (-7546112022 / 1000000000000), orderedInterval (39446819123 / 1000000000000) (39446819135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (457790847835653 / 800000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31693220928 / 1000000000000) (31693220937 / 1000000000000), orderedInterval (10366875967 / 1000000000000) (10366875977 / 1000000000000)))) (orderedInterval (-2407117282 / 1000000000000) (-2407117228 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks1_2 :
    compactCertificate438.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1266273577325791 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2355012185 / 1000000000000) (-2355012184 / 1000000000000), orderedInterval (-44778628750 / 1000000000000) (-44778628749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1073434135094951 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41843135973 / 1000000000000) (-41843092555 / 1000000000000), orderedInterval (25006336363 / 1000000000000) (25006379782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (671705240597453 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49541841305 / 1000000000000) (-49541775290 / 1000000000000), orderedInterval (36707978357 / 1000000000000) (36708044372 / 1000000000000)))) (orderedInterval (6744457178 / 1000000000000) (6744460547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (361245312384051 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (910489500 / 1000000000000) (910489508 / 1000000000000), orderedInterval (-83960073488 / 1000000000000) (-83960073479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (980851295345153 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41548839905 / 1000000000000) (41548839906 / 1000000000000), orderedInterval (29409092307 / 1000000000000) (29409092308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1339268588237281 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22726372949 / 1000000000000) (22726375234 / 1000000000000), orderedInterval (-37248295016 / 1000000000000) (-37248292732 / 1000000000000)))) (orderedInterval (3011948532 / 1000000000000) (3011948755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (566294759402547 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-55934020447 / 1000000000000) (-55934020446 / 1000000000000), orderedInterval (-36790460013 / 1000000000000) (-36790460012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2301956757226387 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32543858722 / 1000000000000) (-32543858669 / 1000000000000), orderedInterval (-6836167200 / 1000000000000) (-6836167147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1537600431796733 / 4000000000000) 1 (IntervalRat.scale (619 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38364922345 / 1000000000000) (38364934222 / 1000000000000), orderedInterval (-13624500307 / 1000000000000) (-13624488430 / 1000000000000)))) (orderedInterval (4108222973 / 1000000000000) (4108225870 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks1 :
    compactCertificate438.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate438.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate438_chunkChecks1_0
    compactCertificate438_chunkChecks1_1 compactCertificate438_chunkChecks1_2

theorem compactCertificate438_chunkChecks2_0 :
    compactCertificate438.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (619 / 2) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30335180068 / 1000000000000) (30335197557 / 1000000000000), orderedInterval (-33764091619 / 1000000000000) (-33764074130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (911905196750719 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28743421488 / 1000000000000) (28743426960 / 1000000000000), orderedInterval (-44406030498 / 1000000000000) (-44406025026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (294891404354527 / 800000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40137798187 / 1000000000000) (-40137793231 / 1000000000000), orderedInterval (10825618015 / 1000000000000) (10825622971 / 1000000000000)))) (orderedInterval (-8786360216 / 1000000000000) (-8786352792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (266091662087933 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95071556330 / 1000000000000) (-95071556329 / 1000000000000), orderedInterval (-22330871675 / 1000000000000) (-22330871674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (714759633256601 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23453871379 / 1000000000000) (-23453871378 / 1000000000000), orderedInterval (-54821826013 / 1000000000000) (-54821826012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1940711444841717 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30161067785 / 1000000000000) (30161143409 / 1000000000000), orderedInterval (-20092133173 / 1000000000000) (-20092057549 / 1000000000000)))) (orderedInterval (5503193698 / 1000000000000) (5503206995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1429519266513821 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (983418445 / 1000000000000) (983418447 / 1000000000000), orderedInterval (42193269384 / 1000000000000) (42193269386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2449505628546833 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16881228473 / 1000000000000) (-16881228472 / 1000000000000), orderedInterval (-27456441873 / 1000000000000) (-27456441872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1804294759402547 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19009010270 / 1000000000000) (-19009009327 / 1000000000000), orderedInterval (32424791443 / 1000000000000) (32424792387 / 1000000000000)))) (orderedInterval (-1071678063 / 1000000000000) (-1071677960 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks2_1 :
    compactCertificate438.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2768252156144381 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30085072509 / 1000000000000) (30085079196 / 1000000000000), orderedInterval (-3865557985 / 1000000000000) (-3865551298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1598251127534549 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39078636572 / 1000000000000) (-39078636558 / 1000000000000), orderedInterval (-8084362775 / 1000000000000) (-8084362761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2836124672438041 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5469149081 / 1000000000000) (-5469149079 / 1000000000000), orderedInterval (29465041024 / 1000000000000) (29465041026 / 1000000000000)))) (orderedInterval (35601295906 / 1000000000000) (35601302404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2649875561408029 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11442255706 / 1000000000000) (-11442255705 / 1000000000000), orderedInterval (-28802049707 / 1000000000000) (-28802049706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1891076236784557 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26987040940 / 1000000000000) (26987060350 / 1000000000000), orderedInterval (-24893700520 / 1000000000000) (-24893681111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2144278899769803 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12057604622 / 1000000000000) (12057604676 / 1000000000000), orderedInterval (-32294113797 / 1000000000000) (-32294113743 / 1000000000000)))) (orderedInterval (-6710838384 / 1000000000000) (-6710833991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1787676194314907 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37728075387 / 1000000000000) (37728075916 / 1000000000000), orderedInterval (-1069192050 / 1000000000000) (-1069191520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1579466132457047 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7546112034 / 1000000000000) (-7546112022 / 1000000000000), orderedInterval (39446819123 / 1000000000000) (39446819135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (457790847835653 / 800000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31693220928 / 1000000000000) (31693220937 / 1000000000000), orderedInterval (10366875967 / 1000000000000) (10366875977 / 1000000000000)))) (orderedInterval (-4377572054 / 1000000000000) (-4377571975 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks2_2 :
    compactCertificate438.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1266273577325791 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2355012185 / 1000000000000) (-2355012184 / 1000000000000), orderedInterval (-44778628750 / 1000000000000) (-44778628749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1073434135094951 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41843135973 / 1000000000000) (-41843092555 / 1000000000000), orderedInterval (25006336363 / 1000000000000) (25006379782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (671705240597453 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49541841305 / 1000000000000) (-49541775290 / 1000000000000), orderedInterval (36707978357 / 1000000000000) (36708044372 / 1000000000000)))) (orderedInterval (-1721469877 / 1000000000000) (-1721467317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (361245312384051 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (910489500 / 1000000000000) (910489508 / 1000000000000), orderedInterval (-83960073488 / 1000000000000) (-83960073479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (980851295345153 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41548839905 / 1000000000000) (41548839906 / 1000000000000), orderedInterval (29409092307 / 1000000000000) (29409092308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1339268588237281 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22726372949 / 1000000000000) (22726375234 / 1000000000000), orderedInterval (-37248295016 / 1000000000000) (-37248292732 / 1000000000000)))) (orderedInterval (2621719854 / 1000000000000) (2621720093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (566294759402547 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-55934020447 / 1000000000000) (-55934020446 / 1000000000000), orderedInterval (-36790460013 / 1000000000000) (-36790460012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2301956757226387 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32543858722 / 1000000000000) (-32543858669 / 1000000000000), orderedInterval (-6836167200 / 1000000000000) (-6836167147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1537600431796733 / 4000000000000) 2 (IntervalRat.scale (619 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38364922345 / 1000000000000) (38364934222 / 1000000000000), orderedInterval (-13624500307 / 1000000000000) (-13624488430 / 1000000000000)))) (orderedInterval (2001979825 / 1000000000000) (2001983464 / 1000000000000))) = true
  rfl'

theorem compactCertificate438_chunkChecks2 :
    compactCertificate438.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate438.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate438_chunkChecks2_0
    compactCertificate438_chunkChecks2_1 compactCertificate438_chunkChecks2_2

theorem compactCertificate438_chunkChecks3_0 :
    compactCertificate438.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (619 / 2) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30335180068 / 1000000000000) (30335197557 / 1000000000000), orderedInterval (-33764091619 / 1000000000000) (-33764074130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (911905196750719 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28743421488 / 1000000000000) (28743426960 / 1000000000000), orderedInterval (-44406030498 / 1000000000000) (-44406025026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (294891404354527 / 800000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40137798187 / 1000000000000) (-40137793231 / 1000000000000), orderedInterval (10825618015 / 1000000000000) (10825622971 / 1000000000000)))) (orderedInterval (12503307185 / 1000000000000) (12503314686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (266091662087933 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95071556330 / 1000000000000) (-95071556329 / 1000000000000), orderedInterval (-22330871675 / 1000000000000) (-22330871674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (714759633256601 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23453871379 / 1000000000000) (-23453871378 / 1000000000000), orderedInterval (-54821826013 / 1000000000000) (-54821826012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1940711444841717 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30161067785 / 1000000000000) (30161143409 / 1000000000000), orderedInterval (-20092133173 / 1000000000000) (-20092057549 / 1000000000000)))) (orderedInterval (-5137373844 / 1000000000000) (-5137353004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1429519266513821 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (983418445 / 1000000000000) (983418447 / 1000000000000), orderedInterval (42193269384 / 1000000000000) (42193269386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2449505628546833 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16881228473 / 1000000000000) (-16881228472 / 1000000000000), orderedInterval (-27456441873 / 1000000000000) (-27456441872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1804294759402547 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19009010270 / 1000000000000) (-19009009327 / 1000000000000), orderedInterval (32424791443 / 1000000000000) (32424792387 / 1000000000000)))) (orderedInterval (-8982207857 / 1000000000000) (-8982207688 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate438_chunkChecks3_1 :
    compactCertificate438.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2768252156144381 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30085072509 / 1000000000000) (30085079196 / 1000000000000), orderedInterval (-3865557985 / 1000000000000) (-3865551298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1598251127534549 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39078636572 / 1000000000000) (-39078636558 / 1000000000000), orderedInterval (-8084362775 / 1000000000000) (-8084362761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2836124672438041 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5469149081 / 1000000000000) (-5469149079 / 1000000000000), orderedInterval (29465041024 / 1000000000000) (29465041026 / 1000000000000)))) (orderedInterval (-56865497237 / 1000000000000) (-56865482734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2649875561408029 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11442255706 / 1000000000000) (-11442255705 / 1000000000000), orderedInterval (-28802049707 / 1000000000000) (-28802049706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1891076236784557 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26987040940 / 1000000000000) (26987060350 / 1000000000000), orderedInterval (-24893700520 / 1000000000000) (-24893681111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2144278899769803 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12057604622 / 1000000000000) (12057604676 / 1000000000000), orderedInterval (-32294113797 / 1000000000000) (-32294113743 / 1000000000000)))) (orderedInterval (2463668642 / 1000000000000) (2463675367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1787676194314907 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37728075387 / 1000000000000) (37728075916 / 1000000000000), orderedInterval (-1069192050 / 1000000000000) (-1069191520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1579466132457047 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7546112034 / 1000000000000) (-7546112022 / 1000000000000), orderedInterval (39446819123 / 1000000000000) (39446819135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (457790847835653 / 800000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31693220928 / 1000000000000) (31693220937 / 1000000000000), orderedInterval (10366875967 / 1000000000000) (10366875977 / 1000000000000)))) (orderedInterval (3061545832 / 1000000000000) (3061545952 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate438_chunkChecks3_2 :
    compactCertificate438.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1266273577325791 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2355012185 / 1000000000000) (-2355012184 / 1000000000000), orderedInterval (-44778628750 / 1000000000000) (-44778628749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1073434135094951 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41843135973 / 1000000000000) (-41843092555 / 1000000000000), orderedInterval (25006336363 / 1000000000000) (25006379782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (671705240597453 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49541841305 / 1000000000000) (-49541775290 / 1000000000000), orderedInterval (36707978357 / 1000000000000) (36708044372 / 1000000000000)))) (orderedInterval (-6924209020 / 1000000000000) (-6924207000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (361245312384051 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (910489500 / 1000000000000) (910489508 / 1000000000000), orderedInterval (-83960073488 / 1000000000000) (-83960073479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (980851295345153 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41548839905 / 1000000000000) (41548839906 / 1000000000000), orderedInterval (29409092307 / 1000000000000) (29409092308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1339268588237281 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22726372949 / 1000000000000) (22726375234 / 1000000000000), orderedInterval (-37248295016 / 1000000000000) (-37248292732 / 1000000000000)))) (orderedInterval (-3329207482 / 1000000000000) (-3329207225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (566294759402547 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-55934020447 / 1000000000000) (-55934020446 / 1000000000000), orderedInterval (-36790460013 / 1000000000000) (-36790460012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2301956757226387 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32543858722 / 1000000000000) (-32543858669 / 1000000000000), orderedInterval (-6836167200 / 1000000000000) (-6836167147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1537600431796733 / 4000000000000) 3 (IntervalRat.scale (619 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38364922345 / 1000000000000) (38364934222 / 1000000000000), orderedInterval (-13624500307 / 1000000000000) (-13624488430 / 1000000000000)))) (orderedInterval (-8460269757 / 1000000000000) (-8460265174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate438_chunkChecks3 :
    compactCertificate438.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate438.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate438_chunkChecks3_0
    compactCertificate438_chunkChecks3_1 compactCertificate438_chunkChecks3_2

theorem compactCertificate438_chunkChecks4_0 :
    compactCertificate438.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (619 / 2) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30335180068 / 1000000000000) (30335197557 / 1000000000000), orderedInterval (-33764091619 / 1000000000000) (-33764074130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (911905196750719 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28743421488 / 1000000000000) (28743426960 / 1000000000000), orderedInterval (-44406030498 / 1000000000000) (-44406025026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (294891404354527 / 800000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40137798187 / 1000000000000) (-40137793231 / 1000000000000), orderedInterval (10825618015 / 1000000000000) (10825622971 / 1000000000000)))) (orderedInterval (7282638351 / 1000000000000) (7282645969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (266091662087933 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95071556330 / 1000000000000) (-95071556329 / 1000000000000), orderedInterval (-22330871675 / 1000000000000) (-22330871674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (714759633256601 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-23453871379 / 1000000000000) (-23453871378 / 1000000000000), orderedInterval (-54821826013 / 1000000000000) (-54821826012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1940711444841717 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30161067785 / 1000000000000) (30161143409 / 1000000000000), orderedInterval (-20092133173 / 1000000000000) (-20092057549 / 1000000000000)))) (orderedInterval (-13008071883 / 1000000000000) (-13008039149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1429519266513821 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (983418445 / 1000000000000) (983418447 / 1000000000000), orderedInterval (42193269384 / 1000000000000) (42193269386 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2449505628546833 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16881228473 / 1000000000000) (-16881228472 / 1000000000000), orderedInterval (-27456441873 / 1000000000000) (-27456441872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1804294759402547 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19009010270 / 1000000000000) (-19009009327 / 1000000000000), orderedInterval (32424791443 / 1000000000000) (32424792387 / 1000000000000)))) (orderedInterval (5965332578 / 1000000000000) (5965332862 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate438_chunkChecks4_1 :
    compactCertificate438.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2768252156144381 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30085072509 / 1000000000000) (30085079196 / 1000000000000), orderedInterval (-3865557985 / 1000000000000) (-3865551298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1598251127534549 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39078636572 / 1000000000000) (-39078636558 / 1000000000000), orderedInterval (-8084362775 / 1000000000000) (-8084362761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2836124672438041 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5469149081 / 1000000000000) (-5469149079 / 1000000000000), orderedInterval (29465041024 / 1000000000000) (29465041026 / 1000000000000)))) (orderedInterval (-162733111390 / 1000000000000) (-162733078937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2649875561408029 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11442255706 / 1000000000000) (-11442255705 / 1000000000000), orderedInterval (-28802049707 / 1000000000000) (-28802049706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1891076236784557 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26987040940 / 1000000000000) (26987060350 / 1000000000000), orderedInterval (-24893700520 / 1000000000000) (-24893681111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2144278899769803 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12057604622 / 1000000000000) (12057604676 / 1000000000000), orderedInterval (-32294113797 / 1000000000000) (-32294113743 / 1000000000000)))) (orderedInterval (17664844901 / 1000000000000) (17664855231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1787676194314907 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37728075387 / 1000000000000) (37728075916 / 1000000000000), orderedInterval (-1069192050 / 1000000000000) (-1069191520 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1579466132457047 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7546112034 / 1000000000000) (-7546112022 / 1000000000000), orderedInterval (39446819123 / 1000000000000) (39446819135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (457790847835653 / 800000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31693220928 / 1000000000000) (31693220937 / 1000000000000), orderedInterval (10366875967 / 1000000000000) (10366875977 / 1000000000000)))) (orderedInterval (12501397430 / 1000000000000) (12501397617 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate438_chunkChecks4_2 :
    compactCertificate438.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1266273577325791 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2355012185 / 1000000000000) (-2355012184 / 1000000000000), orderedInterval (-44778628750 / 1000000000000) (-44778628749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1073434135094951 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41843135973 / 1000000000000) (-41843092555 / 1000000000000), orderedInterval (25006336363 / 1000000000000) (25006379782 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (671705240597453 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49541841305 / 1000000000000) (-49541775290 / 1000000000000), orderedInterval (36707978357 / 1000000000000) (36708044372 / 1000000000000)))) (orderedInterval (1655721042 / 1000000000000) (1655722696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (361245312384051 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (910489500 / 1000000000000) (910489508 / 1000000000000), orderedInterval (-83960073488 / 1000000000000) (-83960073479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (980851295345153 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41548839905 / 1000000000000) (41548839906 / 1000000000000), orderedInterval (29409092307 / 1000000000000) (29409092308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1339268588237281 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22726372949 / 1000000000000) (22726375234 / 1000000000000), orderedInterval (-37248295016 / 1000000000000) (-37248292732 / 1000000000000)))) (orderedInterval (-2735433669 / 1000000000000) (-2735433391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (566294759402547 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-55934020447 / 1000000000000) (-55934020446 / 1000000000000), orderedInterval (-36790460013 / 1000000000000) (-36790460012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2301956757226387 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32543858722 / 1000000000000) (-32543858669 / 1000000000000), orderedInterval (-6836167200 / 1000000000000) (-6836167147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1537600431796733 / 4000000000000) 4 (IntervalRat.scale (619 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38364922345 / 1000000000000) (38364934222 / 1000000000000), orderedInterval (-13624500307 / 1000000000000) (-13624488430 / 1000000000000)))) (orderedInterval (14578549981 / 1000000000000) (14578555804 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate438_chunkChecks4 :
    compactCertificate438.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate438.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate438_chunkChecks4_0
    compactCertificate438_chunkChecks4_1 compactCertificate438_chunkChecks4_2

theorem compactCertificate438_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate438.chunkCheck r b = true :=
  compactCertificate438.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate438_chunkChecks0
    · exact compactCertificate438_chunkChecks1
    · exact compactCertificate438_chunkChecks2
    · exact compactCertificate438_chunkChecks3
    · exact compactCertificate438_chunkChecks4)

theorem compactCertificate438_coefficient0 :
    compactCertificate438.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate438_coefficient1 :
    compactCertificate438.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate438_coefficient2 :
    compactCertificate438.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate438_coefficient3 :
    compactCertificate438.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate438_coefficient4 :
    compactCertificate438.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate438_coefficients : ∀ r : Fin 5,
    compactCertificate438.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate438_coefficient0
  · exact compactCertificate438_coefficient1
  · exact compactCertificate438_coefficient2
  · exact compactCertificate438_coefficient3
  · exact compactCertificate438_coefficient4

theorem compactCertificate438_lower : (1 : ℚ) ≤ compactCertificate438.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate438, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate438_proves {t : ℝ} (ht : t ∈ compactCertificate438.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate438.proves compactCertificate438_states compactCertificate438_chunks
    compactCertificate438_coefficients compactCertificate438_lower ht

end Erdos232
