/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate507 : CompactCertificate where
  left := 378
  right := 379
  center := 757 / 2
  grid := fun i =>
    match i.val with
    | 0 => 121
    | 1 => 89
    | 2 => 144
    | 3 => 26
    | 4 => 70
    | 5 => 189
    | 6 => 139
    | 7 => 239
    | 8 => 176
    | 9 => 270
    | 10 => 156
    | 11 => 276
    | 12 => 258
    | 13 => 184
    | 14 => 209
    | 15 => 174
    | 16 => 154
    | 17 => 223
    | 18 => 123
    | 19 => 105
    | 20 => 65
    | 21 => 35
    | 22 => 96
    | 23 => 130
    | 24 => 55
    | 25 => 224
    | _ => 150
  point := fun i =>
    match i.val with
    | 0 => 757 / 2
    | 1 => 1115205547561057 / 4000000000000
    | 2 => 360634560737281 / 800000000000
    | 3 => 325414197416099 / 4000000000000
    | 4 => 874108307552903 / 4000000000000
    | 5 => 2373374093287851 / 4000000000000
    | 6 => 1748216615106563 / 4000000000000
    | 7 => 2995598967382799 / 4000000000000
    | 8 => 2206544641143341 / 4000000000000
    | 9 => 3385406917934243 / 4000000000000
    | 10 => 1954565595385547 / 4000000000000
    | 11 => 3468410948361223 / 4000000000000
    | 12 => 3240639418393987 / 4000000000000
    | 13 => 2312673200720371 / 4000000000000
    | 14 => 2622324922658709 / 4000000000000
    | 15 => 2186221129396421 / 4000000000000
    | 16 => 1931592669256841 / 4000000000000
    | 17 => 559850842991259 / 800000000000
    | 18 => 1548576895049473 / 4000000000000
    | 19 => 1312745783952953 / 4000000000000
    | 20 => 821455358856659 / 4000000000000
    | 21 => 441781424030253 / 4000000000000
    | 22 => 1199522504969759 / 4000000000000
    | 23 => 1637845430202943 / 4000000000000
    | 24 => 692544641143341 / 4000000000000
    | 25 => 2815155517318861 / 4000000000000
    | _ => 1880393419822499 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (30747330074 / 1000000000000) (30747366843 / 1000000000000), orderedInterval (-27180178881 / 1000000000000) (-27180142112 / 1000000000000))
    | 1 => (orderedInterval (736313050 / 1000000000000) (736313053 / 1000000000000), orderedInterval (-47780796416 / 1000000000000) (-47780796413 / 1000000000000))
    | 2 => (orderedInterval (-27244798041 / 1000000000000) (-27244779380 / 1000000000000), orderedInterval (25913461573 / 1000000000000) (25913480234 / 1000000000000))
    | 3 => (orderedInterval (38954516472 / 1000000000000) (38954516473 / 1000000000000), orderedInterval (79183407746 / 1000000000000) (79183407747 / 1000000000000))
    | 4 => (orderedInterval (-30457583146 / 1000000000000) (-30457575746 / 1000000000000), orderedInterval (44629410784 / 1000000000000) (44629418184 / 1000000000000))
    | 5 => (orderedInterval (-11774673656 / 1000000000000) (-11774673655 / 1000000000000), orderedInterval (-30556294158 / 1000000000000) (-30556294157 / 1000000000000))
    | 6 => (orderedInterval (-34958075677 / 1000000000000) (-34958075675 / 1000000000000), orderedInterval (-15274954496 / 1000000000000) (-15274954495 / 1000000000000))
    | 7 => (orderedInterval (26679619861 / 1000000000000) (26679724167 / 1000000000000), orderedInterval (-11776619590 / 1000000000000) (-11776515284 / 1000000000000))
    | 8 => (orderedInterval (-16256201857 / 1000000000000) (-16256201518 / 1000000000000), orderedInterval (29844141421 / 1000000000000) (29844141759 / 1000000000000))
    | 9 => (orderedInterval (-24355170673 / 1000000000000) (-24355131063 / 1000000000000), orderedInterval (12624659302 / 1000000000000) (12624698912 / 1000000000000))
    | 10 => (orderedInterval (-22184842037 / 1000000000000) (-22184838651 / 1000000000000), orderedInterval (28494954841 / 1000000000000) (28494958227 / 1000000000000))
    | 11 => (orderedInterval (19595698259 / 1000000000000) (19595698260 / 1000000000000), orderedInterval (18702344305 / 1000000000000) (18702344306 / 1000000000000))
    | 12 => (orderedInterval (11281551508 / 1000000000000) (11281551509 / 1000000000000), orderedInterval (25654720082 / 1000000000000) (25654720083 / 1000000000000))
    | 13 => (orderedInterval (26001916114 / 1000000000000) (26001916115 / 1000000000000), orderedInterval (20592991763 / 1000000000000) (20592991764 / 1000000000000))
    | 14 => (orderedInterval (6995786611 / 1000000000000) (6995786614 / 1000000000000), orderedInterval (-30372029452 / 1000000000000) (-30372029449 / 1000000000000))
    | 15 => (orderedInterval (22073276966 / 1000000000000) (22073276967 / 1000000000000), orderedInterval (26009716934 / 1000000000000) (26009716935 / 1000000000000))
    | 16 => (orderedInterval (-4417327527 / 1000000000000) (-4417327524 / 1000000000000), orderedInterval (36043708197 / 1000000000000) (36043708200 / 1000000000000))
    | 17 => (orderedInterval (-712086356 / 1000000000000) (-712086355 / 1000000000000), orderedInterval (-30152306733 / 1000000000000) (-30152306732 / 1000000000000))
    | 18 => (orderedInterval (-40484409189 / 1000000000000) (-40484409073 / 1000000000000), orderedInterval (-2273819541 / 1000000000000) (-2273819425 / 1000000000000))
    | 19 => (orderedInterval (34383992849 / 1000000000000) (34384063113 / 1000000000000), orderedInterval (-27576033057 / 1000000000000) (-27575962793 / 1000000000000))
    | 20 => (orderedInterval (-51822118126 / 1000000000000) (-51822111384 / 1000000000000), orderedInterval (20483526716 / 1000000000000) (20483533459 / 1000000000000))
    | 21 => (orderedInterval (-72599298390 / 1000000000000) (-72599298389 / 1000000000000), orderedInterval (-21884135986 / 1000000000000) (-21884135985 / 1000000000000))
    | 22 => (orderedInterval (-36859845151 / 1000000000000) (-36859741611 / 1000000000000), orderedInterval (27706752841 / 1000000000000) (27706856381 / 1000000000000))
    | 23 => (orderedInterval (38016657374 / 1000000000000) (38016663946 / 1000000000000), orderedInterval (-10510949959 / 1000000000000) (-10510943386 / 1000000000000))
    | 24 => (orderedInterval (-54925346960 / 1000000000000) (-54925346959 / 1000000000000), orderedInterval (-25535458055 / 1000000000000) (-25535458054 / 1000000000000))
    | 25 => (orderedInterval (22740637308 / 1000000000000) (22740637309 / 1000000000000), orderedInterval (19666935813 / 1000000000000) (19666935814 / 1000000000000))
    | _ => (orderedInterval (-12805433711 / 1000000000000) (-12805433626 / 1000000000000), orderedInterval (34513593945 / 1000000000000) (34513594029 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10595270457 / 1000000000000) (10595286153 / 1000000000000)
      | 1 => orderedInterval (-697631124 / 1000000000000) (-697630808 / 1000000000000)
      | 2 => orderedInterval (-1215789775 / 1000000000000) (-1215786528 / 1000000000000)
      | 3 => orderedInterval (5469542380 / 1000000000000) (5469549820 / 1000000000000)
      | 4 => orderedInterval (2219746157 / 1000000000000) (2219746203 / 1000000000000)
      | 5 => orderedInterval (489451652 / 1000000000000) (489451689 / 1000000000000)
      | 6 => orderedInterval (2839931423 / 1000000000000) (2839935734 / 1000000000000)
      | 7 => orderedInterval (-736767779 / 1000000000000) (-736764880 / 1000000000000)
      | _ => orderedInterval (220402691 / 1000000000000) (220402813 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9290150777 / 1000000000000) (-9290134869 / 1000000000000)
      | 1 => orderedInterval (4161379111 / 1000000000000) (4161379320 / 1000000000000)
      | 2 => orderedInterval (1769900413 / 1000000000000) (1769906828 / 1000000000000)
      | 3 => orderedInterval (3800204190 / 1000000000000) (3800220563 / 1000000000000)
      | 4 => orderedInterval (2249473225 / 1000000000000) (2249473299 / 1000000000000)
      | 5 => orderedInterval (-3625272228 / 1000000000000) (-3625272175 / 1000000000000)
      | 6 => orderedInterval (2087005870 / 1000000000000) (2087009545 / 1000000000000)
      | 7 => orderedInterval (491336977 / 1000000000000) (491339425 / 1000000000000)
      | _ => orderedInterval (-11089997199 / 1000000000000) (-11089997032 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9898557673 / 1000000000000) (-9898541470 / 1000000000000)
      | 1 => orderedInterval (-1677790844 / 1000000000000) (-1677790681 / 1000000000000)
      | 2 => orderedInterval (4051396386 / 1000000000000) (4051409081 / 1000000000000)
      | 3 => orderedInterval (-33528198034 / 1000000000000) (-33528161715 / 1000000000000)
      | 4 => orderedInterval (-4703867926 / 1000000000000) (-4703867804 / 1000000000000)
      | 5 => orderedInterval (-871057967 / 1000000000000) (-871057888 / 1000000000000)
      | 6 => orderedInterval (-4817931183 / 1000000000000) (-4817928016 / 1000000000000)
      | 7 => orderedInterval (2769346738 / 1000000000000) (2769348849 / 1000000000000)
      | _ => orderedInterval (2792475890 / 1000000000000) (2792476132 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8408312831 / 1000000000000) (8408329337 / 1000000000000)
      | 1 => orderedInterval (-8668726307 / 1000000000000) (-8668726147 / 1000000000000)
      | 2 => orderedInterval (-5057163591 / 1000000000000) (-5057138492 / 1000000000000)
      | 3 => orderedInterval (-11338786168 / 1000000000000) (-11338705383 / 1000000000000)
      | 4 => orderedInterval (-3185082069 / 1000000000000) (-3185081863 / 1000000000000)
      | 5 => orderedInterval (8260930465 / 1000000000000) (8260930586 / 1000000000000)
      | 6 => orderedInterval (-1500266078 / 1000000000000) (-1500263341 / 1000000000000)
      | 7 => orderedInterval (-724579940 / 1000000000000) (-724578087 / 1000000000000)
      | _ => orderedInterval (22705892017 / 1000000000000) (22705892383 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8927856964 / 1000000000000) (8927873875 / 1000000000000)
      | 1 => orderedInterval (4976275293 / 1000000000000) (4976275489 / 1000000000000)
      | 2 => orderedInterval (-14357816040 / 1000000000000) (-14357766343 / 1000000000000)
      | 3 => orderedInterval (180410431540 / 1000000000000) (180410611857 / 1000000000000)
      | 4 => orderedInterval (8810023624 / 1000000000000) (8810023981 / 1000000000000)
      | 5 => orderedInterval (1521278096 / 1000000000000) (1521278288 / 1000000000000)
      | 6 => orderedInterval (5846744277 / 1000000000000) (5846746659 / 1000000000000)
      | 7 => orderedInterval (-3647284579 / 1000000000000) (-3647282910 / 1000000000000)
      | _ => orderedInterval (-16545322191 / 1000000000000) (-16545321614 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (19184156082 / 1000000000000) (19184190196 / 1000000000000)
    | 1 => orderedInterval (-9446120418 / 1000000000000) (-9446075096 / 1000000000000)
    | 2 => orderedInterval (-45884184613 / 1000000000000) (-45884113512 / 1000000000000)
    | 3 => orderedInterval (8900531160 / 1000000000000) (8900658993 / 1000000000000)
    | _ => orderedInterval (175942186984 / 1000000000000) (175942439282 / 1000000000000)

theorem compactCertificate507_stateChecks0 :
    compactCertificate507.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (757 / 2)) (orderedInterval (30747330074 / 1000000000000) (30747366843 / 1000000000000), orderedInterval (-27180178881 / 1000000000000) (-27180142112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1115205547561057 / 4000000000000)) (orderedInterval (736313050 / 1000000000000) (736313053 / 1000000000000), orderedInterval (-47780796416 / 1000000000000) (-47780796413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (360634560737281 / 800000000000)) (orderedInterval (-27244798041 / 1000000000000) (-27244779380 / 1000000000000), orderedInterval (25913461573 / 1000000000000) (25913480234 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks1 :
    compactCertificate507.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (325414197416099 / 4000000000000)) (orderedInterval (38954516472 / 1000000000000) (38954516473 / 1000000000000), orderedInterval (79183407746 / 1000000000000) (79183407747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (874108307552903 / 4000000000000)) (orderedInterval (-30457583146 / 1000000000000) (-30457575746 / 1000000000000), orderedInterval (44629410784 / 1000000000000) (44629418184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2373374093287851 / 4000000000000)) (orderedInterval (-11774673656 / 1000000000000) (-11774673655 / 1000000000000), orderedInterval (-30556294158 / 1000000000000) (-30556294157 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks2 :
    compactCertificate507.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1748216615106563 / 4000000000000)) (orderedInterval (-34958075677 / 1000000000000) (-34958075675 / 1000000000000), orderedInterval (-15274954496 / 1000000000000) (-15274954495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (2995598967382799 / 4000000000000)) (orderedInterval (26679619861 / 1000000000000) (26679724167 / 1000000000000), orderedInterval (-11776619590 / 1000000000000) (-11776515284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2206544641143341 / 4000000000000)) (orderedInterval (-16256201857 / 1000000000000) (-16256201518 / 1000000000000), orderedInterval (29844141421 / 1000000000000) (29844141759 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks3 :
    compactCertificate507.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3385406917934243 / 4000000000000)) (orderedInterval (-24355170673 / 1000000000000) (-24355131063 / 1000000000000), orderedInterval (12624659302 / 1000000000000) (12624698912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1954565595385547 / 4000000000000)) (orderedInterval (-22184842037 / 1000000000000) (-22184838651 / 1000000000000), orderedInterval (28494954841 / 1000000000000) (28494958227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (3468410948361223 / 4000000000000)) (orderedInterval (19595698259 / 1000000000000) (19595698260 / 1000000000000), orderedInterval (18702344305 / 1000000000000) (18702344306 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks4 :
    compactCertificate507.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (3240639418393987 / 4000000000000)) (orderedInterval (11281551508 / 1000000000000) (11281551509 / 1000000000000), orderedInterval (25654720082 / 1000000000000) (25654720083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2312673200720371 / 4000000000000)) (orderedInterval (26001916114 / 1000000000000) (26001916115 / 1000000000000), orderedInterval (20592991763 / 1000000000000) (20592991764 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2622324922658709 / 4000000000000)) (orderedInterval (6995786611 / 1000000000000) (6995786614 / 1000000000000), orderedInterval (-30372029452 / 1000000000000) (-30372029449 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks5 :
    compactCertificate507.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2186221129396421 / 4000000000000)) (orderedInterval (22073276966 / 1000000000000) (22073276967 / 1000000000000), orderedInterval (26009716934 / 1000000000000) (26009716935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1931592669256841 / 4000000000000)) (orderedInterval (-4417327527 / 1000000000000) (-4417327524 / 1000000000000), orderedInterval (36043708197 / 1000000000000) (36043708200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (559850842991259 / 800000000000)) (orderedInterval (-712086356 / 1000000000000) (-712086355 / 1000000000000), orderedInterval (-30152306733 / 1000000000000) (-30152306732 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks6 :
    compactCertificate507.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1548576895049473 / 4000000000000)) (orderedInterval (-40484409189 / 1000000000000) (-40484409073 / 1000000000000), orderedInterval (-2273819541 / 1000000000000) (-2273819425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1312745783952953 / 4000000000000)) (orderedInterval (34383992849 / 1000000000000) (34384063113 / 1000000000000), orderedInterval (-27576033057 / 1000000000000) (-27575962793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (821455358856659 / 4000000000000)) (orderedInterval (-51822118126 / 1000000000000) (-51822111384 / 1000000000000), orderedInterval (20483526716 / 1000000000000) (20483533459 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks7 :
    compactCertificate507.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (441781424030253 / 4000000000000)) (orderedInterval (-72599298390 / 1000000000000) (-72599298389 / 1000000000000), orderedInterval (-21884135986 / 1000000000000) (-21884135985 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1199522504969759 / 4000000000000)) (orderedInterval (-36859845151 / 1000000000000) (-36859741611 / 1000000000000), orderedInterval (27706752841 / 1000000000000) (27706856381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1637845430202943 / 4000000000000)) (orderedInterval (38016657374 / 1000000000000) (38016663946 / 1000000000000), orderedInterval (-10510949959 / 1000000000000) (-10510943386 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_stateChecks8 :
    compactCertificate507.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (692544641143341 / 4000000000000)) (orderedInterval (-54925346960 / 1000000000000) (-54925346959 / 1000000000000), orderedInterval (-25535458055 / 1000000000000) (-25535458054 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2815155517318861 / 4000000000000)) (orderedInterval (22740637308 / 1000000000000) (22740637309 / 1000000000000), orderedInterval (19666935813 / 1000000000000) (19666935814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1880393419822499 / 4000000000000)) (orderedInterval (-12805433711 / 1000000000000) (-12805433626 / 1000000000000), orderedInterval (34513593945 / 1000000000000) (34513594029 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_states : ∀ j,
    BesselStateValid (compactCertificate507.point j) (compactCertificate507.state j) :=
  compactCertificate507.statesValid_of_checks3 compactCertificate507_stateChecks0
    compactCertificate507_stateChecks1 compactCertificate507_stateChecks2
    compactCertificate507_stateChecks3 compactCertificate507_stateChecks4
    compactCertificate507_stateChecks5 compactCertificate507_stateChecks6
    compactCertificate507_stateChecks7 compactCertificate507_stateChecks8

theorem compactCertificate507_chunkChecks0_0 :
    compactCertificate507.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (757 / 2) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30747330074 / 1000000000000) (30747366843 / 1000000000000), orderedInterval (-27180178881 / 1000000000000) (-27180142112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1115205547561057 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (736313050 / 1000000000000) (736313053 / 1000000000000), orderedInterval (-47780796416 / 1000000000000) (-47780796413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (360634560737281 / 800000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27244798041 / 1000000000000) (-27244779380 / 1000000000000), orderedInterval (25913461573 / 1000000000000) (25913480234 / 1000000000000)))) (orderedInterval (10595270457 / 1000000000000) (10595286153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (325414197416099 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38954516472 / 1000000000000) (38954516473 / 1000000000000), orderedInterval (79183407746 / 1000000000000) (79183407747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (874108307552903 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-30457583146 / 1000000000000) (-30457575746 / 1000000000000), orderedInterval (44629410784 / 1000000000000) (44629418184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2373374093287851 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11774673656 / 1000000000000) (-11774673655 / 1000000000000), orderedInterval (-30556294158 / 1000000000000) (-30556294157 / 1000000000000)))) (orderedInterval (-697631124 / 1000000000000) (-697630808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1748216615106563 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34958075677 / 1000000000000) (-34958075675 / 1000000000000), orderedInterval (-15274954496 / 1000000000000) (-15274954495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2995598967382799 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26679619861 / 1000000000000) (26679724167 / 1000000000000), orderedInterval (-11776619590 / 1000000000000) (-11776515284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2206544641143341 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16256201857 / 1000000000000) (-16256201518 / 1000000000000), orderedInterval (29844141421 / 1000000000000) (29844141759 / 1000000000000)))) (orderedInterval (-1215789775 / 1000000000000) (-1215786528 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks0_1 :
    compactCertificate507.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3385406917934243 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24355170673 / 1000000000000) (-24355131063 / 1000000000000), orderedInterval (12624659302 / 1000000000000) (12624698912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1954565595385547 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22184842037 / 1000000000000) (-22184838651 / 1000000000000), orderedInterval (28494954841 / 1000000000000) (28494958227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3468410948361223 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19595698259 / 1000000000000) (19595698260 / 1000000000000), orderedInterval (18702344305 / 1000000000000) (18702344306 / 1000000000000)))) (orderedInterval (5469542380 / 1000000000000) (5469549820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3240639418393987 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11281551508 / 1000000000000) (11281551509 / 1000000000000), orderedInterval (25654720082 / 1000000000000) (25654720083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2312673200720371 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26001916114 / 1000000000000) (26001916115 / 1000000000000), orderedInterval (20592991763 / 1000000000000) (20592991764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2622324922658709 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6995786611 / 1000000000000) (6995786614 / 1000000000000), orderedInterval (-30372029452 / 1000000000000) (-30372029449 / 1000000000000)))) (orderedInterval (2219746157 / 1000000000000) (2219746203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2186221129396421 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22073276966 / 1000000000000) (22073276967 / 1000000000000), orderedInterval (26009716934 / 1000000000000) (26009716935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1931592669256841 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4417327527 / 1000000000000) (-4417327524 / 1000000000000), orderedInterval (36043708197 / 1000000000000) (36043708200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (559850842991259 / 800000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-712086356 / 1000000000000) (-712086355 / 1000000000000), orderedInterval (-30152306733 / 1000000000000) (-30152306732 / 1000000000000)))) (orderedInterval (489451652 / 1000000000000) (489451689 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks0_2 :
    compactCertificate507.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1548576895049473 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40484409189 / 1000000000000) (-40484409073 / 1000000000000), orderedInterval (-2273819541 / 1000000000000) (-2273819425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1312745783952953 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34383992849 / 1000000000000) (34384063113 / 1000000000000), orderedInterval (-27576033057 / 1000000000000) (-27575962793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (821455358856659 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51822118126 / 1000000000000) (-51822111384 / 1000000000000), orderedInterval (20483526716 / 1000000000000) (20483533459 / 1000000000000)))) (orderedInterval (2839931423 / 1000000000000) (2839935734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (441781424030253 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72599298390 / 1000000000000) (-72599298389 / 1000000000000), orderedInterval (-21884135986 / 1000000000000) (-21884135985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1199522504969759 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36859845151 / 1000000000000) (-36859741611 / 1000000000000), orderedInterval (27706752841 / 1000000000000) (27706856381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1637845430202943 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38016657374 / 1000000000000) (38016663946 / 1000000000000), orderedInterval (-10510949959 / 1000000000000) (-10510943386 / 1000000000000)))) (orderedInterval (-736767779 / 1000000000000) (-736764880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (692544641143341 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54925346960 / 1000000000000) (-54925346959 / 1000000000000), orderedInterval (-25535458055 / 1000000000000) (-25535458054 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2815155517318861 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22740637308 / 1000000000000) (22740637309 / 1000000000000), orderedInterval (19666935813 / 1000000000000) (19666935814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1880393419822499 / 4000000000000) 0 (IntervalRat.scale (757 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12805433711 / 1000000000000) (-12805433626 / 1000000000000), orderedInterval (34513593945 / 1000000000000) (34513594029 / 1000000000000)))) (orderedInterval (220402691 / 1000000000000) (220402813 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks0 :
    compactCertificate507.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate507.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate507_chunkChecks0_0
    compactCertificate507_chunkChecks0_1 compactCertificate507_chunkChecks0_2

theorem compactCertificate507_chunkChecks1_0 :
    compactCertificate507.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (757 / 2) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30747330074 / 1000000000000) (30747366843 / 1000000000000), orderedInterval (-27180178881 / 1000000000000) (-27180142112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1115205547561057 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (736313050 / 1000000000000) (736313053 / 1000000000000), orderedInterval (-47780796416 / 1000000000000) (-47780796413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (360634560737281 / 800000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27244798041 / 1000000000000) (-27244779380 / 1000000000000), orderedInterval (25913461573 / 1000000000000) (25913480234 / 1000000000000)))) (orderedInterval (-9290150777 / 1000000000000) (-9290134869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (325414197416099 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38954516472 / 1000000000000) (38954516473 / 1000000000000), orderedInterval (79183407746 / 1000000000000) (79183407747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (874108307552903 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-30457583146 / 1000000000000) (-30457575746 / 1000000000000), orderedInterval (44629410784 / 1000000000000) (44629418184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2373374093287851 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11774673656 / 1000000000000) (-11774673655 / 1000000000000), orderedInterval (-30556294158 / 1000000000000) (-30556294157 / 1000000000000)))) (orderedInterval (4161379111 / 1000000000000) (4161379320 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1748216615106563 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34958075677 / 1000000000000) (-34958075675 / 1000000000000), orderedInterval (-15274954496 / 1000000000000) (-15274954495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2995598967382799 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26679619861 / 1000000000000) (26679724167 / 1000000000000), orderedInterval (-11776619590 / 1000000000000) (-11776515284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2206544641143341 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16256201857 / 1000000000000) (-16256201518 / 1000000000000), orderedInterval (29844141421 / 1000000000000) (29844141759 / 1000000000000)))) (orderedInterval (1769900413 / 1000000000000) (1769906828 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks1_1 :
    compactCertificate507.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3385406917934243 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24355170673 / 1000000000000) (-24355131063 / 1000000000000), orderedInterval (12624659302 / 1000000000000) (12624698912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1954565595385547 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22184842037 / 1000000000000) (-22184838651 / 1000000000000), orderedInterval (28494954841 / 1000000000000) (28494958227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3468410948361223 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19595698259 / 1000000000000) (19595698260 / 1000000000000), orderedInterval (18702344305 / 1000000000000) (18702344306 / 1000000000000)))) (orderedInterval (3800204190 / 1000000000000) (3800220563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3240639418393987 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11281551508 / 1000000000000) (11281551509 / 1000000000000), orderedInterval (25654720082 / 1000000000000) (25654720083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2312673200720371 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26001916114 / 1000000000000) (26001916115 / 1000000000000), orderedInterval (20592991763 / 1000000000000) (20592991764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2622324922658709 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6995786611 / 1000000000000) (6995786614 / 1000000000000), orderedInterval (-30372029452 / 1000000000000) (-30372029449 / 1000000000000)))) (orderedInterval (2249473225 / 1000000000000) (2249473299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2186221129396421 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22073276966 / 1000000000000) (22073276967 / 1000000000000), orderedInterval (26009716934 / 1000000000000) (26009716935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1931592669256841 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4417327527 / 1000000000000) (-4417327524 / 1000000000000), orderedInterval (36043708197 / 1000000000000) (36043708200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (559850842991259 / 800000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-712086356 / 1000000000000) (-712086355 / 1000000000000), orderedInterval (-30152306733 / 1000000000000) (-30152306732 / 1000000000000)))) (orderedInterval (-3625272228 / 1000000000000) (-3625272175 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks1_2 :
    compactCertificate507.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1548576895049473 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40484409189 / 1000000000000) (-40484409073 / 1000000000000), orderedInterval (-2273819541 / 1000000000000) (-2273819425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1312745783952953 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34383992849 / 1000000000000) (34384063113 / 1000000000000), orderedInterval (-27576033057 / 1000000000000) (-27575962793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (821455358856659 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51822118126 / 1000000000000) (-51822111384 / 1000000000000), orderedInterval (20483526716 / 1000000000000) (20483533459 / 1000000000000)))) (orderedInterval (2087005870 / 1000000000000) (2087009545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (441781424030253 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72599298390 / 1000000000000) (-72599298389 / 1000000000000), orderedInterval (-21884135986 / 1000000000000) (-21884135985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1199522504969759 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36859845151 / 1000000000000) (-36859741611 / 1000000000000), orderedInterval (27706752841 / 1000000000000) (27706856381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1637845430202943 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38016657374 / 1000000000000) (38016663946 / 1000000000000), orderedInterval (-10510949959 / 1000000000000) (-10510943386 / 1000000000000)))) (orderedInterval (491336977 / 1000000000000) (491339425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (692544641143341 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54925346960 / 1000000000000) (-54925346959 / 1000000000000), orderedInterval (-25535458055 / 1000000000000) (-25535458054 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2815155517318861 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22740637308 / 1000000000000) (22740637309 / 1000000000000), orderedInterval (19666935813 / 1000000000000) (19666935814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1880393419822499 / 4000000000000) 1 (IntervalRat.scale (757 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12805433711 / 1000000000000) (-12805433626 / 1000000000000), orderedInterval (34513593945 / 1000000000000) (34513594029 / 1000000000000)))) (orderedInterval (-11089997199 / 1000000000000) (-11089997032 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks1 :
    compactCertificate507.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate507.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate507_chunkChecks1_0
    compactCertificate507_chunkChecks1_1 compactCertificate507_chunkChecks1_2

theorem compactCertificate507_chunkChecks2_0 :
    compactCertificate507.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (757 / 2) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30747330074 / 1000000000000) (30747366843 / 1000000000000), orderedInterval (-27180178881 / 1000000000000) (-27180142112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1115205547561057 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (736313050 / 1000000000000) (736313053 / 1000000000000), orderedInterval (-47780796416 / 1000000000000) (-47780796413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (360634560737281 / 800000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27244798041 / 1000000000000) (-27244779380 / 1000000000000), orderedInterval (25913461573 / 1000000000000) (25913480234 / 1000000000000)))) (orderedInterval (-9898557673 / 1000000000000) (-9898541470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (325414197416099 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38954516472 / 1000000000000) (38954516473 / 1000000000000), orderedInterval (79183407746 / 1000000000000) (79183407747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (874108307552903 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-30457583146 / 1000000000000) (-30457575746 / 1000000000000), orderedInterval (44629410784 / 1000000000000) (44629418184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2373374093287851 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11774673656 / 1000000000000) (-11774673655 / 1000000000000), orderedInterval (-30556294158 / 1000000000000) (-30556294157 / 1000000000000)))) (orderedInterval (-1677790844 / 1000000000000) (-1677790681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1748216615106563 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34958075677 / 1000000000000) (-34958075675 / 1000000000000), orderedInterval (-15274954496 / 1000000000000) (-15274954495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2995598967382799 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26679619861 / 1000000000000) (26679724167 / 1000000000000), orderedInterval (-11776619590 / 1000000000000) (-11776515284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2206544641143341 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16256201857 / 1000000000000) (-16256201518 / 1000000000000), orderedInterval (29844141421 / 1000000000000) (29844141759 / 1000000000000)))) (orderedInterval (4051396386 / 1000000000000) (4051409081 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks2_1 :
    compactCertificate507.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3385406917934243 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24355170673 / 1000000000000) (-24355131063 / 1000000000000), orderedInterval (12624659302 / 1000000000000) (12624698912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1954565595385547 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22184842037 / 1000000000000) (-22184838651 / 1000000000000), orderedInterval (28494954841 / 1000000000000) (28494958227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3468410948361223 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19595698259 / 1000000000000) (19595698260 / 1000000000000), orderedInterval (18702344305 / 1000000000000) (18702344306 / 1000000000000)))) (orderedInterval (-33528198034 / 1000000000000) (-33528161715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3240639418393987 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11281551508 / 1000000000000) (11281551509 / 1000000000000), orderedInterval (25654720082 / 1000000000000) (25654720083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2312673200720371 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26001916114 / 1000000000000) (26001916115 / 1000000000000), orderedInterval (20592991763 / 1000000000000) (20592991764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2622324922658709 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6995786611 / 1000000000000) (6995786614 / 1000000000000), orderedInterval (-30372029452 / 1000000000000) (-30372029449 / 1000000000000)))) (orderedInterval (-4703867926 / 1000000000000) (-4703867804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2186221129396421 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22073276966 / 1000000000000) (22073276967 / 1000000000000), orderedInterval (26009716934 / 1000000000000) (26009716935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1931592669256841 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4417327527 / 1000000000000) (-4417327524 / 1000000000000), orderedInterval (36043708197 / 1000000000000) (36043708200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (559850842991259 / 800000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-712086356 / 1000000000000) (-712086355 / 1000000000000), orderedInterval (-30152306733 / 1000000000000) (-30152306732 / 1000000000000)))) (orderedInterval (-871057967 / 1000000000000) (-871057888 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks2_2 :
    compactCertificate507.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1548576895049473 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40484409189 / 1000000000000) (-40484409073 / 1000000000000), orderedInterval (-2273819541 / 1000000000000) (-2273819425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1312745783952953 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34383992849 / 1000000000000) (34384063113 / 1000000000000), orderedInterval (-27576033057 / 1000000000000) (-27575962793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (821455358856659 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51822118126 / 1000000000000) (-51822111384 / 1000000000000), orderedInterval (20483526716 / 1000000000000) (20483533459 / 1000000000000)))) (orderedInterval (-4817931183 / 1000000000000) (-4817928016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (441781424030253 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72599298390 / 1000000000000) (-72599298389 / 1000000000000), orderedInterval (-21884135986 / 1000000000000) (-21884135985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1199522504969759 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36859845151 / 1000000000000) (-36859741611 / 1000000000000), orderedInterval (27706752841 / 1000000000000) (27706856381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1637845430202943 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38016657374 / 1000000000000) (38016663946 / 1000000000000), orderedInterval (-10510949959 / 1000000000000) (-10510943386 / 1000000000000)))) (orderedInterval (2769346738 / 1000000000000) (2769348849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (692544641143341 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54925346960 / 1000000000000) (-54925346959 / 1000000000000), orderedInterval (-25535458055 / 1000000000000) (-25535458054 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2815155517318861 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22740637308 / 1000000000000) (22740637309 / 1000000000000), orderedInterval (19666935813 / 1000000000000) (19666935814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1880393419822499 / 4000000000000) 2 (IntervalRat.scale (757 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12805433711 / 1000000000000) (-12805433626 / 1000000000000), orderedInterval (34513593945 / 1000000000000) (34513594029 / 1000000000000)))) (orderedInterval (2792475890 / 1000000000000) (2792476132 / 1000000000000))) = true
  rfl'

theorem compactCertificate507_chunkChecks2 :
    compactCertificate507.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate507.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate507_chunkChecks2_0
    compactCertificate507_chunkChecks2_1 compactCertificate507_chunkChecks2_2

theorem compactCertificate507_chunkChecks3_0 :
    compactCertificate507.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (757 / 2) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30747330074 / 1000000000000) (30747366843 / 1000000000000), orderedInterval (-27180178881 / 1000000000000) (-27180142112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1115205547561057 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (736313050 / 1000000000000) (736313053 / 1000000000000), orderedInterval (-47780796416 / 1000000000000) (-47780796413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (360634560737281 / 800000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27244798041 / 1000000000000) (-27244779380 / 1000000000000), orderedInterval (25913461573 / 1000000000000) (25913480234 / 1000000000000)))) (orderedInterval (8408312831 / 1000000000000) (8408329337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (325414197416099 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38954516472 / 1000000000000) (38954516473 / 1000000000000), orderedInterval (79183407746 / 1000000000000) (79183407747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (874108307552903 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-30457583146 / 1000000000000) (-30457575746 / 1000000000000), orderedInterval (44629410784 / 1000000000000) (44629418184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2373374093287851 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11774673656 / 1000000000000) (-11774673655 / 1000000000000), orderedInterval (-30556294158 / 1000000000000) (-30556294157 / 1000000000000)))) (orderedInterval (-8668726307 / 1000000000000) (-8668726147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1748216615106563 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34958075677 / 1000000000000) (-34958075675 / 1000000000000), orderedInterval (-15274954496 / 1000000000000) (-15274954495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2995598967382799 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26679619861 / 1000000000000) (26679724167 / 1000000000000), orderedInterval (-11776619590 / 1000000000000) (-11776515284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2206544641143341 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16256201857 / 1000000000000) (-16256201518 / 1000000000000), orderedInterval (29844141421 / 1000000000000) (29844141759 / 1000000000000)))) (orderedInterval (-5057163591 / 1000000000000) (-5057138492 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate507_chunkChecks3_1 :
    compactCertificate507.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3385406917934243 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24355170673 / 1000000000000) (-24355131063 / 1000000000000), orderedInterval (12624659302 / 1000000000000) (12624698912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1954565595385547 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22184842037 / 1000000000000) (-22184838651 / 1000000000000), orderedInterval (28494954841 / 1000000000000) (28494958227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3468410948361223 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19595698259 / 1000000000000) (19595698260 / 1000000000000), orderedInterval (18702344305 / 1000000000000) (18702344306 / 1000000000000)))) (orderedInterval (-11338786168 / 1000000000000) (-11338705383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3240639418393987 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11281551508 / 1000000000000) (11281551509 / 1000000000000), orderedInterval (25654720082 / 1000000000000) (25654720083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2312673200720371 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26001916114 / 1000000000000) (26001916115 / 1000000000000), orderedInterval (20592991763 / 1000000000000) (20592991764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2622324922658709 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6995786611 / 1000000000000) (6995786614 / 1000000000000), orderedInterval (-30372029452 / 1000000000000) (-30372029449 / 1000000000000)))) (orderedInterval (-3185082069 / 1000000000000) (-3185081863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2186221129396421 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22073276966 / 1000000000000) (22073276967 / 1000000000000), orderedInterval (26009716934 / 1000000000000) (26009716935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1931592669256841 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4417327527 / 1000000000000) (-4417327524 / 1000000000000), orderedInterval (36043708197 / 1000000000000) (36043708200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (559850842991259 / 800000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-712086356 / 1000000000000) (-712086355 / 1000000000000), orderedInterval (-30152306733 / 1000000000000) (-30152306732 / 1000000000000)))) (orderedInterval (8260930465 / 1000000000000) (8260930586 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate507_chunkChecks3_2 :
    compactCertificate507.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1548576895049473 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40484409189 / 1000000000000) (-40484409073 / 1000000000000), orderedInterval (-2273819541 / 1000000000000) (-2273819425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1312745783952953 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34383992849 / 1000000000000) (34384063113 / 1000000000000), orderedInterval (-27576033057 / 1000000000000) (-27575962793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (821455358856659 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51822118126 / 1000000000000) (-51822111384 / 1000000000000), orderedInterval (20483526716 / 1000000000000) (20483533459 / 1000000000000)))) (orderedInterval (-1500266078 / 1000000000000) (-1500263341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (441781424030253 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72599298390 / 1000000000000) (-72599298389 / 1000000000000), orderedInterval (-21884135986 / 1000000000000) (-21884135985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1199522504969759 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36859845151 / 1000000000000) (-36859741611 / 1000000000000), orderedInterval (27706752841 / 1000000000000) (27706856381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1637845430202943 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38016657374 / 1000000000000) (38016663946 / 1000000000000), orderedInterval (-10510949959 / 1000000000000) (-10510943386 / 1000000000000)))) (orderedInterval (-724579940 / 1000000000000) (-724578087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (692544641143341 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54925346960 / 1000000000000) (-54925346959 / 1000000000000), orderedInterval (-25535458055 / 1000000000000) (-25535458054 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2815155517318861 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22740637308 / 1000000000000) (22740637309 / 1000000000000), orderedInterval (19666935813 / 1000000000000) (19666935814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1880393419822499 / 4000000000000) 3 (IntervalRat.scale (757 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12805433711 / 1000000000000) (-12805433626 / 1000000000000), orderedInterval (34513593945 / 1000000000000) (34513594029 / 1000000000000)))) (orderedInterval (22705892017 / 1000000000000) (22705892383 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate507_chunkChecks3 :
    compactCertificate507.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate507.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate507_chunkChecks3_0
    compactCertificate507_chunkChecks3_1 compactCertificate507_chunkChecks3_2

theorem compactCertificate507_chunkChecks4_0 :
    compactCertificate507.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (757 / 2) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30747330074 / 1000000000000) (30747366843 / 1000000000000), orderedInterval (-27180178881 / 1000000000000) (-27180142112 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1115205547561057 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (736313050 / 1000000000000) (736313053 / 1000000000000), orderedInterval (-47780796416 / 1000000000000) (-47780796413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (360634560737281 / 800000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27244798041 / 1000000000000) (-27244779380 / 1000000000000), orderedInterval (25913461573 / 1000000000000) (25913480234 / 1000000000000)))) (orderedInterval (8927856964 / 1000000000000) (8927873875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (325414197416099 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (38954516472 / 1000000000000) (38954516473 / 1000000000000), orderedInterval (79183407746 / 1000000000000) (79183407747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (874108307552903 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-30457583146 / 1000000000000) (-30457575746 / 1000000000000), orderedInterval (44629410784 / 1000000000000) (44629418184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2373374093287851 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-11774673656 / 1000000000000) (-11774673655 / 1000000000000), orderedInterval (-30556294158 / 1000000000000) (-30556294157 / 1000000000000)))) (orderedInterval (4976275293 / 1000000000000) (4976275489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1748216615106563 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34958075677 / 1000000000000) (-34958075675 / 1000000000000), orderedInterval (-15274954496 / 1000000000000) (-15274954495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2995598967382799 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26679619861 / 1000000000000) (26679724167 / 1000000000000), orderedInterval (-11776619590 / 1000000000000) (-11776515284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2206544641143341 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16256201857 / 1000000000000) (-16256201518 / 1000000000000), orderedInterval (29844141421 / 1000000000000) (29844141759 / 1000000000000)))) (orderedInterval (-14357816040 / 1000000000000) (-14357766343 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate507_chunkChecks4_1 :
    compactCertificate507.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3385406917934243 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24355170673 / 1000000000000) (-24355131063 / 1000000000000), orderedInterval (12624659302 / 1000000000000) (12624698912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1954565595385547 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22184842037 / 1000000000000) (-22184838651 / 1000000000000), orderedInterval (28494954841 / 1000000000000) (28494958227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3468410948361223 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19595698259 / 1000000000000) (19595698260 / 1000000000000), orderedInterval (18702344305 / 1000000000000) (18702344306 / 1000000000000)))) (orderedInterval (180410431540 / 1000000000000) (180410611857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3240639418393987 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11281551508 / 1000000000000) (11281551509 / 1000000000000), orderedInterval (25654720082 / 1000000000000) (25654720083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2312673200720371 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26001916114 / 1000000000000) (26001916115 / 1000000000000), orderedInterval (20592991763 / 1000000000000) (20592991764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2622324922658709 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6995786611 / 1000000000000) (6995786614 / 1000000000000), orderedInterval (-30372029452 / 1000000000000) (-30372029449 / 1000000000000)))) (orderedInterval (8810023624 / 1000000000000) (8810023981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2186221129396421 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22073276966 / 1000000000000) (22073276967 / 1000000000000), orderedInterval (26009716934 / 1000000000000) (26009716935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1931592669256841 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-4417327527 / 1000000000000) (-4417327524 / 1000000000000), orderedInterval (36043708197 / 1000000000000) (36043708200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (559850842991259 / 800000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-712086356 / 1000000000000) (-712086355 / 1000000000000), orderedInterval (-30152306733 / 1000000000000) (-30152306732 / 1000000000000)))) (orderedInterval (1521278096 / 1000000000000) (1521278288 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate507_chunkChecks4_2 :
    compactCertificate507.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1548576895049473 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40484409189 / 1000000000000) (-40484409073 / 1000000000000), orderedInterval (-2273819541 / 1000000000000) (-2273819425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1312745783952953 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34383992849 / 1000000000000) (34384063113 / 1000000000000), orderedInterval (-27576033057 / 1000000000000) (-27575962793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (821455358856659 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51822118126 / 1000000000000) (-51822111384 / 1000000000000), orderedInterval (20483526716 / 1000000000000) (20483533459 / 1000000000000)))) (orderedInterval (5846744277 / 1000000000000) (5846746659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (441781424030253 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-72599298390 / 1000000000000) (-72599298389 / 1000000000000), orderedInterval (-21884135986 / 1000000000000) (-21884135985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1199522504969759 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-36859845151 / 1000000000000) (-36859741611 / 1000000000000), orderedInterval (27706752841 / 1000000000000) (27706856381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1637845430202943 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38016657374 / 1000000000000) (38016663946 / 1000000000000), orderedInterval (-10510949959 / 1000000000000) (-10510943386 / 1000000000000)))) (orderedInterval (-3647284579 / 1000000000000) (-3647282910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (692544641143341 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-54925346960 / 1000000000000) (-54925346959 / 1000000000000), orderedInterval (-25535458055 / 1000000000000) (-25535458054 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2815155517318861 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22740637308 / 1000000000000) (22740637309 / 1000000000000), orderedInterval (19666935813 / 1000000000000) (19666935814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1880393419822499 / 4000000000000) 4 (IntervalRat.scale (757 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12805433711 / 1000000000000) (-12805433626 / 1000000000000), orderedInterval (34513593945 / 1000000000000) (34513594029 / 1000000000000)))) (orderedInterval (-16545322191 / 1000000000000) (-16545321614 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate507_chunkChecks4 :
    compactCertificate507.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate507.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate507_chunkChecks4_0
    compactCertificate507_chunkChecks4_1 compactCertificate507_chunkChecks4_2

theorem compactCertificate507_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate507.chunkCheck r b = true :=
  compactCertificate507.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate507_chunkChecks0
    · exact compactCertificate507_chunkChecks1
    · exact compactCertificate507_chunkChecks2
    · exact compactCertificate507_chunkChecks3
    · exact compactCertificate507_chunkChecks4)

theorem compactCertificate507_coefficient0 :
    compactCertificate507.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate507_coefficient1 :
    compactCertificate507.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate507_coefficient2 :
    compactCertificate507.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate507_coefficient3 :
    compactCertificate507.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate507_coefficient4 :
    compactCertificate507.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate507_coefficients : ∀ r : Fin 5,
    compactCertificate507.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate507_coefficient0
  · exact compactCertificate507_coefficient1
  · exact compactCertificate507_coefficient2
  · exact compactCertificate507_coefficient3
  · exact compactCertificate507_coefficient4

theorem compactCertificate507_lower : (1 : ℚ) ≤ compactCertificate507.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate507, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate507_proves {t : ℝ} (ht : t ∈ compactCertificate507.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate507.proves compactCertificate507_states compactCertificate507_chunks
    compactCertificate507_coefficients compactCertificate507_lower ht

end Erdos232
