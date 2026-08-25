/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate351 : CompactCertificate where
  left := 222
  right := 223
  center := 445 / 2
  grid := fun i =>
    match i.val with
    | 0 => 71
    | 1 => 52
    | 2 => 84
    | 3 => 15
    | 4 => 41
    | 5 => 111
    | 6 => 82
    | 7 => 140
    | 8 => 103
    | 9 => 158
    | 10 => 91
    | 11 => 162
    | 12 => 152
    | 13 => 108
    | 14 => 123
    | 15 => 102
    | 16 => 90
    | 17 => 131
    | 18 => 72
    | 19 => 61
    | 20 => 38
    | 21 => 21
    | 22 => 56
    | 23 => 77
    | 24 => 32
    | 25 => 132
    | _ => 88
  point := fun i =>
    match i.val with
    | 0 => 445 / 2
    | 1 => 131113994363189 / 800000000000
    | 2 => 42399571870037 / 160000000000
    | 3 => 38258736552223 / 800000000000
    | 4 => 102768347915731 / 800000000000
    | 5 => 279036055881927 / 800000000000
    | 6 => 205536695831551 / 800000000000
    | 7 => 352190631568123 / 800000000000
    | 8 => 259422025180657 / 800000000000
    | 9 => 398020099994911 / 800000000000
    | 10 => 229797011874919 / 800000000000
    | 11 => 407778830124371 / 800000000000
    | 12 => 380999878780799 / 800000000000
    | 13 => 271899491233967 / 800000000000
    | 14 => 308305043747193 / 800000000000
    | 15 => 257032603059817 / 800000000000
    | 16 => 227096099820157 / 800000000000
    | 17 => 65821301223543 / 160000000000
    | 18 => 182065183169621 / 800000000000
    | 19 => 154338672089581 / 800000000000
    | 20 => 96577974819343 / 800000000000
    | 21 => 51939956061681 / 800000000000
    | 22 => 141027084468043 / 800000000000
    | 23 => 192560427064811 / 800000000000
    | 24 => 81422025180657 / 800000000000
    | 25 => 330976011943697 / 800000000000
    | _ => 221076637205023 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-12286110204 / 1000000000000) (-12286110203 / 1000000000000), orderedInterval (-52032648471 / 1000000000000) (-52032648470 / 1000000000000))
    | 1 => (orderedInterval (60285804513 / 1000000000000) (60285804514 / 1000000000000), orderedInterval (15626846146 / 1000000000000) (15626846147 / 1000000000000))
    | 2 => (orderedInterval (46561467992 / 1000000000000) (46561473110 / 1000000000000), orderedInterval (-15397624022 / 1000000000000) (-15397618904 / 1000000000000))
    | 3 => (orderedInterval (-114922657400 / 1000000000000) (-114922657394 / 1000000000000), orderedInterval (-8994185798 / 1000000000000) (-8994185792 / 1000000000000))
    | 4 => (orderedInterval (-29956881947 / 1000000000000) (-29956881946 / 1000000000000), orderedInterval (-63588774873 / 1000000000000) (-63588774872 / 1000000000000))
    | 5 => (orderedInterval (-32469283865 / 1000000000000) (-32469283864 / 1000000000000), orderedInterval (-27719306106 / 1000000000000) (-27719306105 / 1000000000000))
    | 6 => (orderedInterval (4730936945 / 1000000000000) (4730936946 / 1000000000000), orderedInterval (49543850659 / 1000000000000) (49543850660 / 1000000000000))
    | 7 => (orderedInterval (35448924705 / 1000000000000) (35448924707 / 1000000000000), orderedInterval (13723932344 / 1000000000000) (13723932346 / 1000000000000))
    | 8 => (orderedInterval (-44119337580 / 1000000000000) (-44119337535 / 1000000000000), orderedInterval (-4015595208 / 1000000000000) (-4015595164 / 1000000000000))
    | 9 => (orderedInterval (33378282258 / 1000000000000) (33378308991 / 1000000000000), orderedInterval (-12896760265 / 1000000000000) (-12896733531 / 1000000000000))
    | 10 => (orderedInterval (-39494222640 / 1000000000000) (-39494156651 / 1000000000000), orderedInterval (25690834598 / 1000000000000) (25690900587 / 1000000000000))
    | 11 => (orderedInterval (35340493216 / 1000000000000) (35340493776 / 1000000000000), orderedInterval (-30580507 / 1000000000000) (-30579947 / 1000000000000))
    | 12 => (orderedInterval (-17113078741 / 1000000000000) (-17113078267 / 1000000000000), orderedInterval (32327064226 / 1000000000000) (32327064700 / 1000000000000))
    | 13 => (orderedInterval (42387080504 / 1000000000000) (42387080513 / 1000000000000), orderedInterval (8680456433 / 1000000000000) (8680456442 / 1000000000000))
    | 14 => (orderedInterval (10036456324 / 1000000000000) (10036456357 / 1000000000000), orderedInterval (-39398203301 / 1000000000000) (-39398203268 / 1000000000000))
    | 15 => (orderedInterval (44426435072 / 1000000000000) (44426435442 / 1000000000000), orderedInterval (-2850125104 / 1000000000000) (-2850124733 / 1000000000000))
    | 16 => (orderedInterval (44630603788 / 1000000000000) (44630610980 / 1000000000000), orderedInterval (-15913722873 / 1000000000000) (-15913715682 / 1000000000000))
    | 17 => (orderedInterval (-22843841956 / 1000000000000) (-22843841955 / 1000000000000), orderedInterval (-31998316775 / 1000000000000) (-31998316774 / 1000000000000))
    | 18 => (orderedInterval (43626004168 / 1000000000000) (43626067483 / 1000000000000), orderedInterval (-29997269519 / 1000000000000) (-29997206204 / 1000000000000))
    | 19 => (orderedInterval (-50408211247 / 1000000000000) (-50408189427 / 1000000000000), orderedInterval (27678154558 / 1000000000000) (27678176377 / 1000000000000))
    | 20 => (orderedInterval (61698355329 / 1000000000000) (61698381414 / 1000000000000), orderedInterval (-38553156785 / 1000000000000) (-38553130701 / 1000000000000))
    | 21 => (orderedInterval (25937181089 / 1000000000000) (25937181480 / 1000000000000), orderedInterval (-95766393366 / 1000000000000) (-95766392975 / 1000000000000))
    | 22 => (orderedInterval (54587477654 / 1000000000000) (54587477655 / 1000000000000), orderedInterval (24975457812 / 1000000000000) (24975457813 / 1000000000000))
    | 23 => (orderedInterval (20839825085 / 1000000000000) (20839825954 / 1000000000000), orderedInterval (-47059966199 / 1000000000000) (-47059965330 / 1000000000000))
    | 24 => (orderedInterval (70869236806 / 1000000000000) (70869246297 / 1000000000000), orderedInterval (-35455385697 / 1000000000000) (-35455376206 / 1000000000000))
    | 25 => (orderedInterval (-7220296821 / 1000000000000) (-7220296811 / 1000000000000), orderedInterval (38565670151 / 1000000000000) (38565670161 / 1000000000000))
    | _ => (orderedInterval (29827555273 / 1000000000000) (29827555274 / 1000000000000), orderedInterval (37549554816 / 1000000000000) (37549554817 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1575757228 / 1000000000000) (-1575756911 / 1000000000000)
      | 1 => orderedInterval (2461281008 / 1000000000000) (2461281035 / 1000000000000)
      | 2 => orderedInterval (-2159664018 / 1000000000000) (-2159664003 / 1000000000000)
      | 3 => orderedInterval (-3833260105 / 1000000000000) (-3833250298 / 1000000000000)
      | 4 => orderedInterval (4266397424 / 1000000000000) (4266397461 / 1000000000000)
      | 5 => orderedInterval (-2625932346 / 1000000000000) (-2625931908 / 1000000000000)
      | 6 => orderedInterval (-2113770511 / 1000000000000) (-2113758247 / 1000000000000)
      | 7 => orderedInterval (-3314492389 / 1000000000000) (-3314492288 / 1000000000000)
      | _ => orderedInterval (-4581472641 / 1000000000000) (-4581472520 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-21592790789 / 1000000000000) (-21592790413 / 1000000000000)
      | 1 => orderedInterval (1769596907 / 1000000000000) (1769596939 / 1000000000000)
      | 2 => orderedInterval (-978984799 / 1000000000000) (-978984774 / 1000000000000)
      | 3 => orderedInterval (7571581914 / 1000000000000) (7571599213 / 1000000000000)
      | 4 => orderedInterval (350026513 / 1000000000000) (350026577 / 1000000000000)
      | 5 => orderedInterval (-400432966 / 1000000000000) (-400432404 / 1000000000000)
      | 6 => orderedInterval (2866538240 / 1000000000000) (2866550179 / 1000000000000)
      | 7 => orderedInterval (3968719836 / 1000000000000) (3968719935 / 1000000000000)
      | _ => orderedInterval (-14685337780 / 1000000000000) (-14685337665 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (786359087 / 1000000000000) (786359536 / 1000000000000)
      | 1 => orderedInterval (-5373267662 / 1000000000000) (-5373267619 / 1000000000000)
      | 2 => orderedInterval (6549722384 / 1000000000000) (6549722426 / 1000000000000)
      | 3 => orderedInterval (8131389132 / 1000000000000) (8131421918 / 1000000000000)
      | 4 => orderedInterval (-10617204188 / 1000000000000) (-10617204074 / 1000000000000)
      | 5 => orderedInterval (5088810523 / 1000000000000) (5088811251 / 1000000000000)
      | 6 => orderedInterval (4548533568 / 1000000000000) (4548545441 / 1000000000000)
      | 7 => orderedInterval (2669440877 / 1000000000000) (2669440980 / 1000000000000)
      | _ => orderedInterval (6577441592 / 1000000000000) (6577441735 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (22088219067 / 1000000000000) (22088219600 / 1000000000000)
      | 1 => orderedInterval (-7121151345 / 1000000000000) (-7121151281 / 1000000000000)
      | 2 => orderedInterval (3549837460 / 1000000000000) (3549837535 / 1000000000000)
      | 3 => orderedInterval (-29700624849 / 1000000000000) (-29700559259 / 1000000000000)
      | 4 => orderedInterval (1809149678 / 1000000000000) (1809149887 / 1000000000000)
      | 5 => orderedInterval (3363265973 / 1000000000000) (3363266915 / 1000000000000)
      | 6 => orderedInterval (-3931213172 / 1000000000000) (-3931201297 / 1000000000000)
      | 7 => orderedInterval (-4340117993 / 1000000000000) (-4340117883 / 1000000000000)
      | _ => orderedInterval (33670546757 / 1000000000000) (33670546965 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (594632264 / 1000000000000) (594632901 / 1000000000000)
      | 1 => orderedInterval (13884311044 / 1000000000000) (13884311141 / 1000000000000)
      | 2 => orderedInterval (-21599914521 / 1000000000000) (-21599914385 / 1000000000000)
      | 3 => orderedInterval (-17759721509 / 1000000000000) (-17759584496 / 1000000000000)
      | 4 => orderedInterval (27833906863 / 1000000000000) (27833907260 / 1000000000000)
      | 5 => orderedInterval (-11401554780 / 1000000000000) (-11401553551 / 1000000000000)
      | 6 => orderedInterval (-5812734135 / 1000000000000) (-5812722130 / 1000000000000)
      | 7 => orderedInterval (-2639797051 / 1000000000000) (-2639796932 / 1000000000000)
      | _ => orderedInterval (-6574935489 / 1000000000000) (-6574935160 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13476670806 / 1000000000000) (-13476647679 / 1000000000000)
    | 1 => orderedInterval (-21131082924 / 1000000000000) (-21131052413 / 1000000000000)
    | 2 => orderedInterval (18361225313 / 1000000000000) (18361271594 / 1000000000000)
    | 3 => orderedInterval (19387911576 / 1000000000000) (19387991182 / 1000000000000)
    | _ => orderedInterval (-23475807314 / 1000000000000) (-23475655352 / 1000000000000)

theorem compactCertificate351_stateChecks0 :
    compactCertificate351.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (445 / 2)) (orderedInterval (-12286110204 / 1000000000000) (-12286110203 / 1000000000000), orderedInterval (-52032648471 / 1000000000000) (-52032648470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (131113994363189 / 800000000000)) (orderedInterval (60285804513 / 1000000000000) (60285804514 / 1000000000000), orderedInterval (15626846146 / 1000000000000) (15626846147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (42399571870037 / 160000000000)) (orderedInterval (46561467992 / 1000000000000) (46561473110 / 1000000000000), orderedInterval (-15397624022 / 1000000000000) (-15397618904 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks1 :
    compactCertificate351.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (38258736552223 / 800000000000)) (orderedInterval (-114922657400 / 1000000000000) (-114922657394 / 1000000000000), orderedInterval (-8994185798 / 1000000000000) (-8994185792 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (102768347915731 / 800000000000)) (orderedInterval (-29956881947 / 1000000000000) (-29956881946 / 1000000000000), orderedInterval (-63588774873 / 1000000000000) (-63588774872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (279036055881927 / 800000000000)) (orderedInterval (-32469283865 / 1000000000000) (-32469283864 / 1000000000000), orderedInterval (-27719306106 / 1000000000000) (-27719306105 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks2 :
    compactCertificate351.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (205536695831551 / 800000000000)) (orderedInterval (4730936945 / 1000000000000) (4730936946 / 1000000000000), orderedInterval (49543850659 / 1000000000000) (49543850660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (352190631568123 / 800000000000)) (orderedInterval (35448924705 / 1000000000000) (35448924707 / 1000000000000), orderedInterval (13723932344 / 1000000000000) (13723932346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (259422025180657 / 800000000000)) (orderedInterval (-44119337580 / 1000000000000) (-44119337535 / 1000000000000), orderedInterval (-4015595208 / 1000000000000) (-4015595164 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks3 :
    compactCertificate351.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (398020099994911 / 800000000000)) (orderedInterval (33378282258 / 1000000000000) (33378308991 / 1000000000000), orderedInterval (-12896760265 / 1000000000000) (-12896733531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (229797011874919 / 800000000000)) (orderedInterval (-39494222640 / 1000000000000) (-39494156651 / 1000000000000), orderedInterval (25690834598 / 1000000000000) (25690900587 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (407778830124371 / 800000000000)) (orderedInterval (35340493216 / 1000000000000) (35340493776 / 1000000000000), orderedInterval (-30580507 / 1000000000000) (-30579947 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks4 :
    compactCertificate351.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (380999878780799 / 800000000000)) (orderedInterval (-17113078741 / 1000000000000) (-17113078267 / 1000000000000), orderedInterval (32327064226 / 1000000000000) (32327064700 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (271899491233967 / 800000000000)) (orderedInterval (42387080504 / 1000000000000) (42387080513 / 1000000000000), orderedInterval (8680456433 / 1000000000000) (8680456442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308305043747193 / 800000000000)) (orderedInterval (10036456324 / 1000000000000) (10036456357 / 1000000000000), orderedInterval (-39398203301 / 1000000000000) (-39398203268 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks5 :
    compactCertificate351.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (257032603059817 / 800000000000)) (orderedInterval (44426435072 / 1000000000000) (44426435442 / 1000000000000), orderedInterval (-2850125104 / 1000000000000) (-2850124733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (227096099820157 / 800000000000)) (orderedInterval (44630603788 / 1000000000000) (44630610980 / 1000000000000), orderedInterval (-15913722873 / 1000000000000) (-15913715682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (65821301223543 / 160000000000)) (orderedInterval (-22843841956 / 1000000000000) (-22843841955 / 1000000000000), orderedInterval (-31998316775 / 1000000000000) (-31998316774 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks6 :
    compactCertificate351.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (182065183169621 / 800000000000)) (orderedInterval (43626004168 / 1000000000000) (43626067483 / 1000000000000), orderedInterval (-29997269519 / 1000000000000) (-29997206204 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (154338672089581 / 800000000000)) (orderedInterval (-50408211247 / 1000000000000) (-50408189427 / 1000000000000), orderedInterval (27678154558 / 1000000000000) (27678176377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (96577974819343 / 800000000000)) (orderedInterval (61698355329 / 1000000000000) (61698381414 / 1000000000000), orderedInterval (-38553156785 / 1000000000000) (-38553130701 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks7 :
    compactCertificate351.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (51939956061681 / 800000000000)) (orderedInterval (25937181089 / 1000000000000) (25937181480 / 1000000000000), orderedInterval (-95766393366 / 1000000000000) (-95766392975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (141027084468043 / 800000000000)) (orderedInterval (54587477654 / 1000000000000) (54587477655 / 1000000000000), orderedInterval (24975457812 / 1000000000000) (24975457813 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (192560427064811 / 800000000000)) (orderedInterval (20839825085 / 1000000000000) (20839825954 / 1000000000000), orderedInterval (-47059966199 / 1000000000000) (-47059965330 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_stateChecks8 :
    compactCertificate351.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (81422025180657 / 800000000000)) (orderedInterval (70869236806 / 1000000000000) (70869246297 / 1000000000000), orderedInterval (-35455385697 / 1000000000000) (-35455376206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (330976011943697 / 800000000000)) (orderedInterval (-7220296821 / 1000000000000) (-7220296811 / 1000000000000), orderedInterval (38565670151 / 1000000000000) (38565670161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (221076637205023 / 800000000000)) (orderedInterval (29827555273 / 1000000000000) (29827555274 / 1000000000000), orderedInterval (37549554816 / 1000000000000) (37549554817 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_states : ∀ j,
    BesselStateValid (compactCertificate351.point j) (compactCertificate351.state j) :=
  compactCertificate351.statesValid_of_checks3 compactCertificate351_stateChecks0
    compactCertificate351_stateChecks1 compactCertificate351_stateChecks2
    compactCertificate351_stateChecks3 compactCertificate351_stateChecks4
    compactCertificate351_stateChecks5 compactCertificate351_stateChecks6
    compactCertificate351_stateChecks7 compactCertificate351_stateChecks8

theorem compactCertificate351_chunkChecks0_0 :
    compactCertificate351.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (445 / 2) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12286110204 / 1000000000000) (-12286110203 / 1000000000000), orderedInterval (-52032648471 / 1000000000000) (-52032648470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (131113994363189 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60285804513 / 1000000000000) (60285804514 / 1000000000000), orderedInterval (15626846146 / 1000000000000) (15626846147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (42399571870037 / 160000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46561467992 / 1000000000000) (46561473110 / 1000000000000), orderedInterval (-15397624022 / 1000000000000) (-15397618904 / 1000000000000)))) (orderedInterval (-1575757228 / 1000000000000) (-1575756911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (38258736552223 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114922657400 / 1000000000000) (-114922657394 / 1000000000000), orderedInterval (-8994185798 / 1000000000000) (-8994185792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (102768347915731 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29956881947 / 1000000000000) (-29956881946 / 1000000000000), orderedInterval (-63588774873 / 1000000000000) (-63588774872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (279036055881927 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-32469283865 / 1000000000000) (-32469283864 / 1000000000000), orderedInterval (-27719306106 / 1000000000000) (-27719306105 / 1000000000000)))) (orderedInterval (2461281008 / 1000000000000) (2461281035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (205536695831551 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4730936945 / 1000000000000) (4730936946 / 1000000000000), orderedInterval (49543850659 / 1000000000000) (49543850660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (352190631568123 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35448924705 / 1000000000000) (35448924707 / 1000000000000), orderedInterval (13723932344 / 1000000000000) (13723932346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (259422025180657 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44119337580 / 1000000000000) (-44119337535 / 1000000000000), orderedInterval (-4015595208 / 1000000000000) (-4015595164 / 1000000000000)))) (orderedInterval (-2159664018 / 1000000000000) (-2159664003 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks0_1 :
    compactCertificate351.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (398020099994911 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33378282258 / 1000000000000) (33378308991 / 1000000000000), orderedInterval (-12896760265 / 1000000000000) (-12896733531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (229797011874919 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39494222640 / 1000000000000) (-39494156651 / 1000000000000), orderedInterval (25690834598 / 1000000000000) (25690900587 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (407778830124371 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35340493216 / 1000000000000) (35340493776 / 1000000000000), orderedInterval (-30580507 / 1000000000000) (-30579947 / 1000000000000)))) (orderedInterval (-3833260105 / 1000000000000) (-3833250298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (380999878780799 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17113078741 / 1000000000000) (-17113078267 / 1000000000000), orderedInterval (32327064226 / 1000000000000) (32327064700 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (271899491233967 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42387080504 / 1000000000000) (42387080513 / 1000000000000), orderedInterval (8680456433 / 1000000000000) (8680456442 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (308305043747193 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10036456324 / 1000000000000) (10036456357 / 1000000000000), orderedInterval (-39398203301 / 1000000000000) (-39398203268 / 1000000000000)))) (orderedInterval (4266397424 / 1000000000000) (4266397461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (257032603059817 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44426435072 / 1000000000000) (44426435442 / 1000000000000), orderedInterval (-2850125104 / 1000000000000) (-2850124733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (227096099820157 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (44630603788 / 1000000000000) (44630610980 / 1000000000000), orderedInterval (-15913722873 / 1000000000000) (-15913715682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (65821301223543 / 160000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22843841956 / 1000000000000) (-22843841955 / 1000000000000), orderedInterval (-31998316775 / 1000000000000) (-31998316774 / 1000000000000)))) (orderedInterval (-2625932346 / 1000000000000) (-2625931908 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks0_2 :
    compactCertificate351.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (182065183169621 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43626004168 / 1000000000000) (43626067483 / 1000000000000), orderedInterval (-29997269519 / 1000000000000) (-29997206204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (154338672089581 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50408211247 / 1000000000000) (-50408189427 / 1000000000000), orderedInterval (27678154558 / 1000000000000) (27678176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (96577974819343 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61698355329 / 1000000000000) (61698381414 / 1000000000000), orderedInterval (-38553156785 / 1000000000000) (-38553130701 / 1000000000000)))) (orderedInterval (-2113770511 / 1000000000000) (-2113758247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (51939956061681 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25937181089 / 1000000000000) (25937181480 / 1000000000000), orderedInterval (-95766393366 / 1000000000000) (-95766392975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (141027084468043 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54587477654 / 1000000000000) (54587477655 / 1000000000000), orderedInterval (24975457812 / 1000000000000) (24975457813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (192560427064811 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20839825085 / 1000000000000) (20839825954 / 1000000000000), orderedInterval (-47059966199 / 1000000000000) (-47059965330 / 1000000000000)))) (orderedInterval (-3314492389 / 1000000000000) (-3314492288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (81422025180657 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70869236806 / 1000000000000) (70869246297 / 1000000000000), orderedInterval (-35455385697 / 1000000000000) (-35455376206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (330976011943697 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7220296821 / 1000000000000) (-7220296811 / 1000000000000), orderedInterval (38565670151 / 1000000000000) (38565670161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (221076637205023 / 800000000000) 0 (IntervalRat.scale (445 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29827555273 / 1000000000000) (29827555274 / 1000000000000), orderedInterval (37549554816 / 1000000000000) (37549554817 / 1000000000000)))) (orderedInterval (-4581472641 / 1000000000000) (-4581472520 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks0 :
    compactCertificate351.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate351.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate351_chunkChecks0_0
    compactCertificate351_chunkChecks0_1 compactCertificate351_chunkChecks0_2

theorem compactCertificate351_chunkChecks1_0 :
    compactCertificate351.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (445 / 2) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12286110204 / 1000000000000) (-12286110203 / 1000000000000), orderedInterval (-52032648471 / 1000000000000) (-52032648470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (131113994363189 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60285804513 / 1000000000000) (60285804514 / 1000000000000), orderedInterval (15626846146 / 1000000000000) (15626846147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (42399571870037 / 160000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46561467992 / 1000000000000) (46561473110 / 1000000000000), orderedInterval (-15397624022 / 1000000000000) (-15397618904 / 1000000000000)))) (orderedInterval (-21592790789 / 1000000000000) (-21592790413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (38258736552223 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114922657400 / 1000000000000) (-114922657394 / 1000000000000), orderedInterval (-8994185798 / 1000000000000) (-8994185792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (102768347915731 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29956881947 / 1000000000000) (-29956881946 / 1000000000000), orderedInterval (-63588774873 / 1000000000000) (-63588774872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (279036055881927 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-32469283865 / 1000000000000) (-32469283864 / 1000000000000), orderedInterval (-27719306106 / 1000000000000) (-27719306105 / 1000000000000)))) (orderedInterval (1769596907 / 1000000000000) (1769596939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (205536695831551 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4730936945 / 1000000000000) (4730936946 / 1000000000000), orderedInterval (49543850659 / 1000000000000) (49543850660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (352190631568123 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35448924705 / 1000000000000) (35448924707 / 1000000000000), orderedInterval (13723932344 / 1000000000000) (13723932346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (259422025180657 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44119337580 / 1000000000000) (-44119337535 / 1000000000000), orderedInterval (-4015595208 / 1000000000000) (-4015595164 / 1000000000000)))) (orderedInterval (-978984799 / 1000000000000) (-978984774 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks1_1 :
    compactCertificate351.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (398020099994911 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33378282258 / 1000000000000) (33378308991 / 1000000000000), orderedInterval (-12896760265 / 1000000000000) (-12896733531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (229797011874919 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39494222640 / 1000000000000) (-39494156651 / 1000000000000), orderedInterval (25690834598 / 1000000000000) (25690900587 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (407778830124371 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35340493216 / 1000000000000) (35340493776 / 1000000000000), orderedInterval (-30580507 / 1000000000000) (-30579947 / 1000000000000)))) (orderedInterval (7571581914 / 1000000000000) (7571599213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (380999878780799 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17113078741 / 1000000000000) (-17113078267 / 1000000000000), orderedInterval (32327064226 / 1000000000000) (32327064700 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (271899491233967 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42387080504 / 1000000000000) (42387080513 / 1000000000000), orderedInterval (8680456433 / 1000000000000) (8680456442 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (308305043747193 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10036456324 / 1000000000000) (10036456357 / 1000000000000), orderedInterval (-39398203301 / 1000000000000) (-39398203268 / 1000000000000)))) (orderedInterval (350026513 / 1000000000000) (350026577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (257032603059817 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44426435072 / 1000000000000) (44426435442 / 1000000000000), orderedInterval (-2850125104 / 1000000000000) (-2850124733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (227096099820157 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (44630603788 / 1000000000000) (44630610980 / 1000000000000), orderedInterval (-15913722873 / 1000000000000) (-15913715682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (65821301223543 / 160000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22843841956 / 1000000000000) (-22843841955 / 1000000000000), orderedInterval (-31998316775 / 1000000000000) (-31998316774 / 1000000000000)))) (orderedInterval (-400432966 / 1000000000000) (-400432404 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks1_2 :
    compactCertificate351.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (182065183169621 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43626004168 / 1000000000000) (43626067483 / 1000000000000), orderedInterval (-29997269519 / 1000000000000) (-29997206204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (154338672089581 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50408211247 / 1000000000000) (-50408189427 / 1000000000000), orderedInterval (27678154558 / 1000000000000) (27678176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (96577974819343 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61698355329 / 1000000000000) (61698381414 / 1000000000000), orderedInterval (-38553156785 / 1000000000000) (-38553130701 / 1000000000000)))) (orderedInterval (2866538240 / 1000000000000) (2866550179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (51939956061681 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25937181089 / 1000000000000) (25937181480 / 1000000000000), orderedInterval (-95766393366 / 1000000000000) (-95766392975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (141027084468043 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54587477654 / 1000000000000) (54587477655 / 1000000000000), orderedInterval (24975457812 / 1000000000000) (24975457813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (192560427064811 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20839825085 / 1000000000000) (20839825954 / 1000000000000), orderedInterval (-47059966199 / 1000000000000) (-47059965330 / 1000000000000)))) (orderedInterval (3968719836 / 1000000000000) (3968719935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (81422025180657 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70869236806 / 1000000000000) (70869246297 / 1000000000000), orderedInterval (-35455385697 / 1000000000000) (-35455376206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (330976011943697 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7220296821 / 1000000000000) (-7220296811 / 1000000000000), orderedInterval (38565670151 / 1000000000000) (38565670161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (221076637205023 / 800000000000) 1 (IntervalRat.scale (445 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29827555273 / 1000000000000) (29827555274 / 1000000000000), orderedInterval (37549554816 / 1000000000000) (37549554817 / 1000000000000)))) (orderedInterval (-14685337780 / 1000000000000) (-14685337665 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks1 :
    compactCertificate351.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate351.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate351_chunkChecks1_0
    compactCertificate351_chunkChecks1_1 compactCertificate351_chunkChecks1_2

theorem compactCertificate351_chunkChecks2_0 :
    compactCertificate351.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (445 / 2) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12286110204 / 1000000000000) (-12286110203 / 1000000000000), orderedInterval (-52032648471 / 1000000000000) (-52032648470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (131113994363189 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60285804513 / 1000000000000) (60285804514 / 1000000000000), orderedInterval (15626846146 / 1000000000000) (15626846147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (42399571870037 / 160000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46561467992 / 1000000000000) (46561473110 / 1000000000000), orderedInterval (-15397624022 / 1000000000000) (-15397618904 / 1000000000000)))) (orderedInterval (786359087 / 1000000000000) (786359536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (38258736552223 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114922657400 / 1000000000000) (-114922657394 / 1000000000000), orderedInterval (-8994185798 / 1000000000000) (-8994185792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (102768347915731 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29956881947 / 1000000000000) (-29956881946 / 1000000000000), orderedInterval (-63588774873 / 1000000000000) (-63588774872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (279036055881927 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-32469283865 / 1000000000000) (-32469283864 / 1000000000000), orderedInterval (-27719306106 / 1000000000000) (-27719306105 / 1000000000000)))) (orderedInterval (-5373267662 / 1000000000000) (-5373267619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (205536695831551 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4730936945 / 1000000000000) (4730936946 / 1000000000000), orderedInterval (49543850659 / 1000000000000) (49543850660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (352190631568123 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35448924705 / 1000000000000) (35448924707 / 1000000000000), orderedInterval (13723932344 / 1000000000000) (13723932346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (259422025180657 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44119337580 / 1000000000000) (-44119337535 / 1000000000000), orderedInterval (-4015595208 / 1000000000000) (-4015595164 / 1000000000000)))) (orderedInterval (6549722384 / 1000000000000) (6549722426 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks2_1 :
    compactCertificate351.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (398020099994911 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33378282258 / 1000000000000) (33378308991 / 1000000000000), orderedInterval (-12896760265 / 1000000000000) (-12896733531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (229797011874919 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39494222640 / 1000000000000) (-39494156651 / 1000000000000), orderedInterval (25690834598 / 1000000000000) (25690900587 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (407778830124371 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35340493216 / 1000000000000) (35340493776 / 1000000000000), orderedInterval (-30580507 / 1000000000000) (-30579947 / 1000000000000)))) (orderedInterval (8131389132 / 1000000000000) (8131421918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (380999878780799 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17113078741 / 1000000000000) (-17113078267 / 1000000000000), orderedInterval (32327064226 / 1000000000000) (32327064700 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (271899491233967 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42387080504 / 1000000000000) (42387080513 / 1000000000000), orderedInterval (8680456433 / 1000000000000) (8680456442 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (308305043747193 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10036456324 / 1000000000000) (10036456357 / 1000000000000), orderedInterval (-39398203301 / 1000000000000) (-39398203268 / 1000000000000)))) (orderedInterval (-10617204188 / 1000000000000) (-10617204074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (257032603059817 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44426435072 / 1000000000000) (44426435442 / 1000000000000), orderedInterval (-2850125104 / 1000000000000) (-2850124733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (227096099820157 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (44630603788 / 1000000000000) (44630610980 / 1000000000000), orderedInterval (-15913722873 / 1000000000000) (-15913715682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (65821301223543 / 160000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22843841956 / 1000000000000) (-22843841955 / 1000000000000), orderedInterval (-31998316775 / 1000000000000) (-31998316774 / 1000000000000)))) (orderedInterval (5088810523 / 1000000000000) (5088811251 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks2_2 :
    compactCertificate351.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (182065183169621 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43626004168 / 1000000000000) (43626067483 / 1000000000000), orderedInterval (-29997269519 / 1000000000000) (-29997206204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (154338672089581 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50408211247 / 1000000000000) (-50408189427 / 1000000000000), orderedInterval (27678154558 / 1000000000000) (27678176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (96577974819343 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61698355329 / 1000000000000) (61698381414 / 1000000000000), orderedInterval (-38553156785 / 1000000000000) (-38553130701 / 1000000000000)))) (orderedInterval (4548533568 / 1000000000000) (4548545441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (51939956061681 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25937181089 / 1000000000000) (25937181480 / 1000000000000), orderedInterval (-95766393366 / 1000000000000) (-95766392975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (141027084468043 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54587477654 / 1000000000000) (54587477655 / 1000000000000), orderedInterval (24975457812 / 1000000000000) (24975457813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (192560427064811 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20839825085 / 1000000000000) (20839825954 / 1000000000000), orderedInterval (-47059966199 / 1000000000000) (-47059965330 / 1000000000000)))) (orderedInterval (2669440877 / 1000000000000) (2669440980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (81422025180657 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70869236806 / 1000000000000) (70869246297 / 1000000000000), orderedInterval (-35455385697 / 1000000000000) (-35455376206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (330976011943697 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7220296821 / 1000000000000) (-7220296811 / 1000000000000), orderedInterval (38565670151 / 1000000000000) (38565670161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (221076637205023 / 800000000000) 2 (IntervalRat.scale (445 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29827555273 / 1000000000000) (29827555274 / 1000000000000), orderedInterval (37549554816 / 1000000000000) (37549554817 / 1000000000000)))) (orderedInterval (6577441592 / 1000000000000) (6577441735 / 1000000000000))) = true
  rfl'

theorem compactCertificate351_chunkChecks2 :
    compactCertificate351.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate351.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate351_chunkChecks2_0
    compactCertificate351_chunkChecks2_1 compactCertificate351_chunkChecks2_2

theorem compactCertificate351_chunkChecks3_0 :
    compactCertificate351.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (445 / 2) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12286110204 / 1000000000000) (-12286110203 / 1000000000000), orderedInterval (-52032648471 / 1000000000000) (-52032648470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (131113994363189 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60285804513 / 1000000000000) (60285804514 / 1000000000000), orderedInterval (15626846146 / 1000000000000) (15626846147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (42399571870037 / 160000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46561467992 / 1000000000000) (46561473110 / 1000000000000), orderedInterval (-15397624022 / 1000000000000) (-15397618904 / 1000000000000)))) (orderedInterval (22088219067 / 1000000000000) (22088219600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (38258736552223 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114922657400 / 1000000000000) (-114922657394 / 1000000000000), orderedInterval (-8994185798 / 1000000000000) (-8994185792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (102768347915731 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29956881947 / 1000000000000) (-29956881946 / 1000000000000), orderedInterval (-63588774873 / 1000000000000) (-63588774872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (279036055881927 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-32469283865 / 1000000000000) (-32469283864 / 1000000000000), orderedInterval (-27719306106 / 1000000000000) (-27719306105 / 1000000000000)))) (orderedInterval (-7121151345 / 1000000000000) (-7121151281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (205536695831551 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4730936945 / 1000000000000) (4730936946 / 1000000000000), orderedInterval (49543850659 / 1000000000000) (49543850660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (352190631568123 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35448924705 / 1000000000000) (35448924707 / 1000000000000), orderedInterval (13723932344 / 1000000000000) (13723932346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (259422025180657 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44119337580 / 1000000000000) (-44119337535 / 1000000000000), orderedInterval (-4015595208 / 1000000000000) (-4015595164 / 1000000000000)))) (orderedInterval (3549837460 / 1000000000000) (3549837535 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate351_chunkChecks3_1 :
    compactCertificate351.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (398020099994911 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33378282258 / 1000000000000) (33378308991 / 1000000000000), orderedInterval (-12896760265 / 1000000000000) (-12896733531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (229797011874919 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39494222640 / 1000000000000) (-39494156651 / 1000000000000), orderedInterval (25690834598 / 1000000000000) (25690900587 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (407778830124371 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35340493216 / 1000000000000) (35340493776 / 1000000000000), orderedInterval (-30580507 / 1000000000000) (-30579947 / 1000000000000)))) (orderedInterval (-29700624849 / 1000000000000) (-29700559259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (380999878780799 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17113078741 / 1000000000000) (-17113078267 / 1000000000000), orderedInterval (32327064226 / 1000000000000) (32327064700 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (271899491233967 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42387080504 / 1000000000000) (42387080513 / 1000000000000), orderedInterval (8680456433 / 1000000000000) (8680456442 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (308305043747193 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10036456324 / 1000000000000) (10036456357 / 1000000000000), orderedInterval (-39398203301 / 1000000000000) (-39398203268 / 1000000000000)))) (orderedInterval (1809149678 / 1000000000000) (1809149887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (257032603059817 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44426435072 / 1000000000000) (44426435442 / 1000000000000), orderedInterval (-2850125104 / 1000000000000) (-2850124733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (227096099820157 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (44630603788 / 1000000000000) (44630610980 / 1000000000000), orderedInterval (-15913722873 / 1000000000000) (-15913715682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (65821301223543 / 160000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22843841956 / 1000000000000) (-22843841955 / 1000000000000), orderedInterval (-31998316775 / 1000000000000) (-31998316774 / 1000000000000)))) (orderedInterval (3363265973 / 1000000000000) (3363266915 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate351_chunkChecks3_2 :
    compactCertificate351.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (182065183169621 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43626004168 / 1000000000000) (43626067483 / 1000000000000), orderedInterval (-29997269519 / 1000000000000) (-29997206204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (154338672089581 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50408211247 / 1000000000000) (-50408189427 / 1000000000000), orderedInterval (27678154558 / 1000000000000) (27678176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (96577974819343 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61698355329 / 1000000000000) (61698381414 / 1000000000000), orderedInterval (-38553156785 / 1000000000000) (-38553130701 / 1000000000000)))) (orderedInterval (-3931213172 / 1000000000000) (-3931201297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (51939956061681 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25937181089 / 1000000000000) (25937181480 / 1000000000000), orderedInterval (-95766393366 / 1000000000000) (-95766392975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (141027084468043 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54587477654 / 1000000000000) (54587477655 / 1000000000000), orderedInterval (24975457812 / 1000000000000) (24975457813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (192560427064811 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20839825085 / 1000000000000) (20839825954 / 1000000000000), orderedInterval (-47059966199 / 1000000000000) (-47059965330 / 1000000000000)))) (orderedInterval (-4340117993 / 1000000000000) (-4340117883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (81422025180657 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70869236806 / 1000000000000) (70869246297 / 1000000000000), orderedInterval (-35455385697 / 1000000000000) (-35455376206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (330976011943697 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7220296821 / 1000000000000) (-7220296811 / 1000000000000), orderedInterval (38565670151 / 1000000000000) (38565670161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (221076637205023 / 800000000000) 3 (IntervalRat.scale (445 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29827555273 / 1000000000000) (29827555274 / 1000000000000), orderedInterval (37549554816 / 1000000000000) (37549554817 / 1000000000000)))) (orderedInterval (33670546757 / 1000000000000) (33670546965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate351_chunkChecks3 :
    compactCertificate351.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate351.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate351_chunkChecks3_0
    compactCertificate351_chunkChecks3_1 compactCertificate351_chunkChecks3_2

theorem compactCertificate351_chunkChecks4_0 :
    compactCertificate351.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (445 / 2) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12286110204 / 1000000000000) (-12286110203 / 1000000000000), orderedInterval (-52032648471 / 1000000000000) (-52032648470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (131113994363189 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60285804513 / 1000000000000) (60285804514 / 1000000000000), orderedInterval (15626846146 / 1000000000000) (15626846147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (42399571870037 / 160000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46561467992 / 1000000000000) (46561473110 / 1000000000000), orderedInterval (-15397624022 / 1000000000000) (-15397618904 / 1000000000000)))) (orderedInterval (594632264 / 1000000000000) (594632901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (38258736552223 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-114922657400 / 1000000000000) (-114922657394 / 1000000000000), orderedInterval (-8994185798 / 1000000000000) (-8994185792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (102768347915731 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29956881947 / 1000000000000) (-29956881946 / 1000000000000), orderedInterval (-63588774873 / 1000000000000) (-63588774872 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (279036055881927 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-32469283865 / 1000000000000) (-32469283864 / 1000000000000), orderedInterval (-27719306106 / 1000000000000) (-27719306105 / 1000000000000)))) (orderedInterval (13884311044 / 1000000000000) (13884311141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (205536695831551 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (4730936945 / 1000000000000) (4730936946 / 1000000000000), orderedInterval (49543850659 / 1000000000000) (49543850660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (352190631568123 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35448924705 / 1000000000000) (35448924707 / 1000000000000), orderedInterval (13723932344 / 1000000000000) (13723932346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (259422025180657 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44119337580 / 1000000000000) (-44119337535 / 1000000000000), orderedInterval (-4015595208 / 1000000000000) (-4015595164 / 1000000000000)))) (orderedInterval (-21599914521 / 1000000000000) (-21599914385 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate351_chunkChecks4_1 :
    compactCertificate351.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (398020099994911 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33378282258 / 1000000000000) (33378308991 / 1000000000000), orderedInterval (-12896760265 / 1000000000000) (-12896733531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (229797011874919 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39494222640 / 1000000000000) (-39494156651 / 1000000000000), orderedInterval (25690834598 / 1000000000000) (25690900587 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (407778830124371 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35340493216 / 1000000000000) (35340493776 / 1000000000000), orderedInterval (-30580507 / 1000000000000) (-30579947 / 1000000000000)))) (orderedInterval (-17759721509 / 1000000000000) (-17759584496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (380999878780799 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17113078741 / 1000000000000) (-17113078267 / 1000000000000), orderedInterval (32327064226 / 1000000000000) (32327064700 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (271899491233967 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (42387080504 / 1000000000000) (42387080513 / 1000000000000), orderedInterval (8680456433 / 1000000000000) (8680456442 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (308305043747193 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10036456324 / 1000000000000) (10036456357 / 1000000000000), orderedInterval (-39398203301 / 1000000000000) (-39398203268 / 1000000000000)))) (orderedInterval (27833906863 / 1000000000000) (27833907260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (257032603059817 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44426435072 / 1000000000000) (44426435442 / 1000000000000), orderedInterval (-2850125104 / 1000000000000) (-2850124733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (227096099820157 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (44630603788 / 1000000000000) (44630610980 / 1000000000000), orderedInterval (-15913722873 / 1000000000000) (-15913715682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (65821301223543 / 160000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22843841956 / 1000000000000) (-22843841955 / 1000000000000), orderedInterval (-31998316775 / 1000000000000) (-31998316774 / 1000000000000)))) (orderedInterval (-11401554780 / 1000000000000) (-11401553551 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate351_chunkChecks4_2 :
    compactCertificate351.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (182065183169621 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43626004168 / 1000000000000) (43626067483 / 1000000000000), orderedInterval (-29997269519 / 1000000000000) (-29997206204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (154338672089581 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50408211247 / 1000000000000) (-50408189427 / 1000000000000), orderedInterval (27678154558 / 1000000000000) (27678176377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (96577974819343 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61698355329 / 1000000000000) (61698381414 / 1000000000000), orderedInterval (-38553156785 / 1000000000000) (-38553130701 / 1000000000000)))) (orderedInterval (-5812734135 / 1000000000000) (-5812722130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (51939956061681 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25937181089 / 1000000000000) (25937181480 / 1000000000000), orderedInterval (-95766393366 / 1000000000000) (-95766392975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (141027084468043 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54587477654 / 1000000000000) (54587477655 / 1000000000000), orderedInterval (24975457812 / 1000000000000) (24975457813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (192560427064811 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20839825085 / 1000000000000) (20839825954 / 1000000000000), orderedInterval (-47059966199 / 1000000000000) (-47059965330 / 1000000000000)))) (orderedInterval (-2639797051 / 1000000000000) (-2639796932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (81422025180657 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (70869236806 / 1000000000000) (70869246297 / 1000000000000), orderedInterval (-35455385697 / 1000000000000) (-35455376206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (330976011943697 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7220296821 / 1000000000000) (-7220296811 / 1000000000000), orderedInterval (38565670151 / 1000000000000) (38565670161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (221076637205023 / 800000000000) 4 (IntervalRat.scale (445 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29827555273 / 1000000000000) (29827555274 / 1000000000000), orderedInterval (37549554816 / 1000000000000) (37549554817 / 1000000000000)))) (orderedInterval (-6574935489 / 1000000000000) (-6574935160 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate351_chunkChecks4 :
    compactCertificate351.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate351.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate351_chunkChecks4_0
    compactCertificate351_chunkChecks4_1 compactCertificate351_chunkChecks4_2

theorem compactCertificate351_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate351.chunkCheck r b = true :=
  compactCertificate351.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate351_chunkChecks0
    · exact compactCertificate351_chunkChecks1
    · exact compactCertificate351_chunkChecks2
    · exact compactCertificate351_chunkChecks3
    · exact compactCertificate351_chunkChecks4)

theorem compactCertificate351_coefficient0 :
    compactCertificate351.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate351_coefficient1 :
    compactCertificate351.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate351_coefficient2 :
    compactCertificate351.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate351_coefficient3 :
    compactCertificate351.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate351_coefficient4 :
    compactCertificate351.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate351_coefficients : ∀ r : Fin 5,
    compactCertificate351.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate351_coefficient0
  · exact compactCertificate351_coefficient1
  · exact compactCertificate351_coefficient2
  · exact compactCertificate351_coefficient3
  · exact compactCertificate351_coefficient4

theorem compactCertificate351_lower : (1 : ℚ) ≤ compactCertificate351.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate351, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate351_proves {t : ℝ} (ht : t ∈ compactCertificate351.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate351.proves compactCertificate351_states compactCertificate351_chunks
    compactCertificate351_coefficients compactCertificate351_lower ht

end Erdos232
