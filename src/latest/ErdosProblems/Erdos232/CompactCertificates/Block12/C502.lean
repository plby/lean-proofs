/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate502 : CompactCertificate where
  left := 373
  right := 374
  center := 747 / 2
  grid := fun i =>
    match i.val with
    | 0 => 119
    | 1 => 88
    | 2 => 142
    | 3 => 26
    | 4 => 69
    | 5 => 186
    | 6 => 137
    | 7 => 235
    | 8 => 173
    | 9 => 266
    | 10 => 154
    | 11 => 272
    | 12 => 255
    | 13 => 182
    | 14 => 206
    | 15 => 172
    | 16 => 152
    | 17 => 220
    | 18 => 122
    | 19 => 103
    | 20 => 65
    | 21 => 35
    | 22 => 94
    | 23 => 129
    | 24 => 54
    | 25 => 221
    | _ => 148
  point := fun i =>
    match i.val with
    | 0 => 747 / 2
    | 1 => 1100473638082047 / 4000000000000
    | 2 => 355870563897951 / 800000000000
    | 3 => 321115462972029 / 4000000000000
    | 4 => 862561302169113 / 4000000000000
    | 5 => 2342021727458421 / 4000000000000
    | 6 => 1725122604338973 / 4000000000000
    | 7 => 2956026986307729 / 4000000000000
    | 8 => 2177396098988211 / 4000000000000
    | 9 => 3340685558384253 / 4000000000000
    | 10 => 1928745706410837 / 4000000000000
    | 11 => 3422593102279833 / 4000000000000
    | 12 => 3197830443250077 / 4000000000000
    | 13 => 2282122696087341 / 4000000000000
    | 14 => 2587683906507339 / 4000000000000
    | 15 => 2157341061636891 / 4000000000000
    | 16 => 1906076253546711 / 4000000000000
    | 17 => 552455191168389 / 800000000000
    | 18 => 1528120132895583 / 4000000000000
    | 19 => 1295404360122663 / 4000000000000
    | 20 => 810603901011789 / 4000000000000
    | 21 => 435945473910963 / 4000000000000
    | 22 => 1183676765141889 / 4000000000000
    | 23 => 1616209427161953 / 4000000000000
    | 24 => 683396098988211 / 4000000000000
    | 25 => 2777967201370131 / 4000000000000
    | _ => 1855553348226429 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-17418149279 / 1000000000000) (-17418149278 / 1000000000000), orderedInterval (-37407681331 / 1000000000000) (-37407681330 / 1000000000000))
    | 1 => (orderedInterval (-25421561968 / 1000000000000) (-25421558471 / 1000000000000), orderedInterval (40884056543 / 1000000000000) (40884060040 / 1000000000000))
    | 2 => (orderedInterval (-17564259915 / 1000000000000) (-17564259367 / 1000000000000), orderedInterval (33525321574 / 1000000000000) (33525322122 / 1000000000000))
    | 3 => (orderedInterval (-51647230648 / 1000000000000) (-51647212968 / 1000000000000), orderedInterval (72866251866 / 1000000000000) (72866269546 / 1000000000000))
    | 4 => (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))
    | 5 => (orderedInterval (30577902943 / 1000000000000) (30577949108 / 1000000000000), orderedInterval (-12366703591 / 1000000000000) (-12366657426 / 1000000000000))
    | 6 => (orderedInterval (-38240477909 / 1000000000000) (-38240476790 / 1000000000000), orderedInterval (3756443520 / 1000000000000) (3756444638 / 1000000000000))
    | 7 => (orderedInterval (-29309161323 / 1000000000000) (-29309160122 / 1000000000000), orderedInterval (-1537784919 / 1000000000000) (-1537783717 / 1000000000000))
    | 8 => (orderedInterval (-34119314359 / 1000000000000) (-34119312803 / 1000000000000), orderedInterval (2350507055 / 1000000000000) (2350508612 / 1000000000000))
    | 9 => (orderedInterval (7974010856 / 1000000000000) (7974010857 / 1000000000000), orderedInterval (26427738189 / 1000000000000) (26427738190 / 1000000000000))
    | 10 => (orderedInterval (-26903820044 / 1000000000000) (-26903800145 / 1000000000000), orderedInterval (24450462656 / 1000000000000) (24450482555 / 1000000000000))
    | 11 => (orderedInterval (25627360893 / 1000000000000) (25627472385 / 1000000000000), orderedInterval (-9356109134 / 1000000000000) (-9355997641 / 1000000000000))
    | 12 => (orderedInterval (21445754187 / 1000000000000) (21445759585 / 1000000000000), orderedInterval (-18354464687 / 1000000000000) (-18354459290 / 1000000000000))
    | 13 => (orderedInterval (-14650150013 / 1000000000000) (-14650149849 / 1000000000000), orderedInterval (30033020694 / 1000000000000) (30033020858 / 1000000000000))
    | 14 => (orderedInterval (16077153202 / 1000000000000) (16077153203 / 1000000000000), orderedInterval (26924571881 / 1000000000000) (26924571882 / 1000000000000))
    | 15 => (orderedInterval (-7949726998 / 1000000000000) (-7949726990 / 1000000000000), orderedInterval (33431625068 / 1000000000000) (33431625076 / 1000000000000))
    | 16 => (orderedInterval (-7901029249 / 1000000000000) (-7901029239 / 1000000000000), orderedInterval (35695179470 / 1000000000000) (35695179480 / 1000000000000))
    | 17 => (orderedInterval (6145780164 / 1000000000000) (6145780165 / 1000000000000), orderedInterval (29729483001 / 1000000000000) (29729483002 / 1000000000000))
    | 18 => (orderedInterval (-18093433204 / 1000000000000) (-18093432597 / 1000000000000), orderedInterval (36616595503 / 1000000000000) (36616596109 / 1000000000000))
    | 19 => (orderedInterval (-38504355380 / 1000000000000) (-38504355379 / 1000000000000), orderedInterval (-21922197950 / 1000000000000) (-21922197949 / 1000000000000))
    | 20 => (orderedInterval (38927416561 / 1000000000000) (38927456440 / 1000000000000), orderedInterval (-40421170101 / 1000000000000) (-40421130221 / 1000000000000))
    | 21 => (orderedInterval (14067888291 / 1000000000000) (14067888391 / 1000000000000), orderedInterval (-75187309180 / 1000000000000) (-75187309080 / 1000000000000))
    | 22 => (orderedInterval (45663125068 / 1000000000000) (45663125078 / 1000000000000), orderedInterval (8059547474 / 1000000000000) (8059547484 / 1000000000000))
    | 23 => (orderedInterval (16475174395 / 1000000000000) (16475174750 / 1000000000000), orderedInterval (-36133497920 / 1000000000000) (-36133497564 / 1000000000000))
    | 24 => (orderedInterval (55814399425 / 1000000000000) (55814408139 / 1000000000000), orderedInterval (-24880832521 / 1000000000000) (-24880823808 / 1000000000000))
    | 25 => (orderedInterval (-25229311741 / 1000000000000) (-25229311740 / 1000000000000), orderedInterval (-16719568934 / 1000000000000) (-16719568933 / 1000000000000))
    | _ => (orderedInterval (-10317652222 / 1000000000000) (-10317652191 / 1000000000000), orderedInterval (35590642435 / 1000000000000) (35590642466 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8171515065 / 1000000000000) (-8171514973 / 1000000000000)
      | 1 => orderedInterval (-942979548 / 1000000000000) (-942976014 / 1000000000000)
      | 2 => orderedInterval (79415243 / 1000000000000) (79415339 / 1000000000000)
      | 3 => orderedInterval (232843148 / 1000000000000) (232860620 / 1000000000000)
      | 4 => orderedInterval (-1853881993 / 1000000000000) (-1853881835 / 1000000000000)
      | 5 => orderedInterval (517705054 / 1000000000000) (517705091 / 1000000000000)
      | 6 => orderedInterval (6339640491 / 1000000000000) (6339641980 / 1000000000000)
      | 7 => orderedInterval (-2558357021 / 1000000000000) (-2558356946 / 1000000000000)
      | _ => orderedInterval (4326043511 / 1000000000000) (4326043673 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12203424269 / 1000000000000) (-12203424177 / 1000000000000)
      | 1 => orderedInterval (129361366 / 1000000000000) (129366612 / 1000000000000)
      | 2 => orderedInterval (176639943 / 1000000000000) (176640108 / 1000000000000)
      | 3 => orderedInterval (-11208538555 / 1000000000000) (-11208500035 / 1000000000000)
      | 4 => orderedInterval (4811433656 / 1000000000000) (4811433961 / 1000000000000)
      | 5 => orderedInterval (-641293935 / 1000000000000) (-641293882 / 1000000000000)
      | 6 => orderedInterval (-5626553375 / 1000000000000) (-5626552484 / 1000000000000)
      | 7 => orderedInterval (3256002357 / 1000000000000) (3256002428 / 1000000000000)
      | _ => orderedInterval (-5831727422 / 1000000000000) (-5831727245 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8527155534 / 1000000000000) (8527155632 / 1000000000000)
      | 1 => orderedInterval (5092167154 / 1000000000000) (5092175318 / 1000000000000)
      | 2 => orderedInterval (-1788027140 / 1000000000000) (-1788026850 / 1000000000000)
      | 3 => orderedInterval (-8682965469 / 1000000000000) (-8682879071 / 1000000000000)
      | 4 => orderedInterval (5237494914 / 1000000000000) (5237495517 / 1000000000000)
      | 5 => orderedInterval (-1080756429 / 1000000000000) (-1080756350 / 1000000000000)
      | 6 => orderedInterval (-5023120551 / 1000000000000) (-5023119982 / 1000000000000)
      | 7 => orderedInterval (2141342888 / 1000000000000) (2141342960 / 1000000000000)
      | _ => orderedInterval (-10141557386 / 1000000000000) (-10141557151 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11328345814 / 1000000000000) (11328345921 / 1000000000000)
      | 1 => orderedInterval (-3032891885 / 1000000000000) (-3032879110 / 1000000000000)
      | 2 => orderedInterval (-538470618 / 1000000000000) (-538470096 / 1000000000000)
      | 3 => orderedInterval (64617669521 / 1000000000000) (64617864923 / 1000000000000)
      | 4 => orderedInterval (-12677857244 / 1000000000000) (-12677856029 / 1000000000000)
      | 5 => orderedInterval (-1728543092 / 1000000000000) (-1728542971 / 1000000000000)
      | 6 => orderedInterval (5679830780 / 1000000000000) (5679831173 / 1000000000000)
      | 7 => orderedInterval (-3455173908 / 1000000000000) (-3455173832 / 1000000000000)
      | _ => orderedInterval (4085632402 / 1000000000000) (4085632750 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9108113096 / 1000000000000) (-9108112975 / 1000000000000)
      | 1 => orderedInterval (-13035348523 / 1000000000000) (-13035328471 / 1000000000000)
      | 2 => orderedInterval (10137436856 / 1000000000000) (10137437814 / 1000000000000)
      | 3 => orderedInterval (59037782992 / 1000000000000) (59038227871 / 1000000000000)
      | 4 => orderedInterval (-16333491858 / 1000000000000) (-16333489371 / 1000000000000)
      | 5 => orderedInterval (2646934542 / 1000000000000) (2646934732 / 1000000000000)
      | 6 => orderedInterval (4477668765 / 1000000000000) (4477669065 / 1000000000000)
      | 7 => orderedInterval (-2120851502 / 1000000000000) (-2120851421 / 1000000000000)
      | _ => orderedInterval (29148884949 / 1000000000000) (29148885498 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2031086180 / 1000000000000) (-2031063065 / 1000000000000)
    | 1 => orderedInterval (-27138100234 / 1000000000000) (-27138054714 / 1000000000000)
    | 2 => orderedInterval (-5718266485 / 1000000000000) (-5718169977 / 1000000000000)
    | 3 => orderedInterval (64278541770 / 1000000000000) (64278752729 / 1000000000000)
    | _ => orderedInterval (64850903125 / 1000000000000) (64851372742 / 1000000000000)

theorem compactCertificate502_stateChecks0 :
    compactCertificate502.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (747 / 2)) (orderedInterval (-17418149279 / 1000000000000) (-17418149278 / 1000000000000), orderedInterval (-37407681331 / 1000000000000) (-37407681330 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1100473638082047 / 4000000000000)) (orderedInterval (-25421561968 / 1000000000000) (-25421558471 / 1000000000000), orderedInterval (40884056543 / 1000000000000) (40884060040 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (355870563897951 / 800000000000)) (orderedInterval (-17564259915 / 1000000000000) (-17564259367 / 1000000000000), orderedInterval (33525321574 / 1000000000000) (33525322122 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks1 :
    compactCertificate502.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (321115462972029 / 4000000000000)) (orderedInterval (-51647230648 / 1000000000000) (-51647212968 / 1000000000000), orderedInterval (72866251866 / 1000000000000) (72866269546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (862561302169113 / 4000000000000)) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2342021727458421 / 4000000000000)) (orderedInterval (30577902943 / 1000000000000) (30577949108 / 1000000000000), orderedInterval (-12366703591 / 1000000000000) (-12366657426 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks2 :
    compactCertificate502.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1725122604338973 / 4000000000000)) (orderedInterval (-38240477909 / 1000000000000) (-38240476790 / 1000000000000), orderedInterval (3756443520 / 1000000000000) (3756444638 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2956026986307729 / 4000000000000)) (orderedInterval (-29309161323 / 1000000000000) (-29309160122 / 1000000000000), orderedInterval (-1537784919 / 1000000000000) (-1537783717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2177396098988211 / 4000000000000)) (orderedInterval (-34119314359 / 1000000000000) (-34119312803 / 1000000000000), orderedInterval (2350507055 / 1000000000000) (2350508612 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks3 :
    compactCertificate502.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3340685558384253 / 4000000000000)) (orderedInterval (7974010856 / 1000000000000) (7974010857 / 1000000000000), orderedInterval (26427738189 / 1000000000000) (26427738190 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1928745706410837 / 4000000000000)) (orderedInterval (-26903820044 / 1000000000000) (-26903800145 / 1000000000000), orderedInterval (24450462656 / 1000000000000) (24450482555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3422593102279833 / 4000000000000)) (orderedInterval (25627360893 / 1000000000000) (25627472385 / 1000000000000), orderedInterval (-9356109134 / 1000000000000) (-9355997641 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks4 :
    compactCertificate502.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (3197830443250077 / 4000000000000)) (orderedInterval (21445754187 / 1000000000000) (21445759585 / 1000000000000), orderedInterval (-18354464687 / 1000000000000) (-18354459290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2282122696087341 / 4000000000000)) (orderedInterval (-14650150013 / 1000000000000) (-14650149849 / 1000000000000), orderedInterval (30033020694 / 1000000000000) (30033020858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2587683906507339 / 4000000000000)) (orderedInterval (16077153202 / 1000000000000) (16077153203 / 1000000000000), orderedInterval (26924571881 / 1000000000000) (26924571882 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks5 :
    compactCertificate502.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2157341061636891 / 4000000000000)) (orderedInterval (-7949726998 / 1000000000000) (-7949726990 / 1000000000000), orderedInterval (33431625068 / 1000000000000) (33431625076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1906076253546711 / 4000000000000)) (orderedInterval (-7901029249 / 1000000000000) (-7901029239 / 1000000000000), orderedInterval (35695179470 / 1000000000000) (35695179480 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (552455191168389 / 800000000000)) (orderedInterval (6145780164 / 1000000000000) (6145780165 / 1000000000000), orderedInterval (29729483001 / 1000000000000) (29729483002 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks6 :
    compactCertificate502.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1528120132895583 / 4000000000000)) (orderedInterval (-18093433204 / 1000000000000) (-18093432597 / 1000000000000), orderedInterval (36616595503 / 1000000000000) (36616596109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1295404360122663 / 4000000000000)) (orderedInterval (-38504355380 / 1000000000000) (-38504355379 / 1000000000000), orderedInterval (-21922197950 / 1000000000000) (-21922197949 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (810603901011789 / 4000000000000)) (orderedInterval (38927416561 / 1000000000000) (38927456440 / 1000000000000), orderedInterval (-40421170101 / 1000000000000) (-40421130221 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks7 :
    compactCertificate502.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (435945473910963 / 4000000000000)) (orderedInterval (14067888291 / 1000000000000) (14067888391 / 1000000000000), orderedInterval (-75187309180 / 1000000000000) (-75187309080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1183676765141889 / 4000000000000)) (orderedInterval (45663125068 / 1000000000000) (45663125078 / 1000000000000), orderedInterval (8059547474 / 1000000000000) (8059547484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1616209427161953 / 4000000000000)) (orderedInterval (16475174395 / 1000000000000) (16475174750 / 1000000000000), orderedInterval (-36133497920 / 1000000000000) (-36133497564 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_stateChecks8 :
    compactCertificate502.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (683396098988211 / 4000000000000)) (orderedInterval (55814399425 / 1000000000000) (55814408139 / 1000000000000), orderedInterval (-24880832521 / 1000000000000) (-24880823808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2777967201370131 / 4000000000000)) (orderedInterval (-25229311741 / 1000000000000) (-25229311740 / 1000000000000), orderedInterval (-16719568934 / 1000000000000) (-16719568933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1855553348226429 / 4000000000000)) (orderedInterval (-10317652222 / 1000000000000) (-10317652191 / 1000000000000), orderedInterval (35590642435 / 1000000000000) (35590642466 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_states : ∀ j,
    BesselStateValid (compactCertificate502.point j) (compactCertificate502.state j) :=
  compactCertificate502.statesValid_of_checks3 compactCertificate502_stateChecks0
    compactCertificate502_stateChecks1 compactCertificate502_stateChecks2
    compactCertificate502_stateChecks3 compactCertificate502_stateChecks4
    compactCertificate502_stateChecks5 compactCertificate502_stateChecks6
    compactCertificate502_stateChecks7 compactCertificate502_stateChecks8

theorem compactCertificate502_chunkChecks0_0 :
    compactCertificate502.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (747 / 2) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17418149279 / 1000000000000) (-17418149278 / 1000000000000), orderedInterval (-37407681331 / 1000000000000) (-37407681330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1100473638082047 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25421561968 / 1000000000000) (-25421558471 / 1000000000000), orderedInterval (40884056543 / 1000000000000) (40884060040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (355870563897951 / 800000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17564259915 / 1000000000000) (-17564259367 / 1000000000000), orderedInterval (33525321574 / 1000000000000) (33525322122 / 1000000000000)))) (orderedInterval (-8171515065 / 1000000000000) (-8171514973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (321115462972029 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51647230648 / 1000000000000) (-51647212968 / 1000000000000), orderedInterval (72866251866 / 1000000000000) (72866269546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2342021727458421 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30577902943 / 1000000000000) (30577949108 / 1000000000000), orderedInterval (-12366703591 / 1000000000000) (-12366657426 / 1000000000000)))) (orderedInterval (-942979548 / 1000000000000) (-942976014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1725122604338973 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38240477909 / 1000000000000) (-38240476790 / 1000000000000), orderedInterval (3756443520 / 1000000000000) (3756444638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2956026986307729 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29309161323 / 1000000000000) (-29309160122 / 1000000000000), orderedInterval (-1537784919 / 1000000000000) (-1537783717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2177396098988211 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34119314359 / 1000000000000) (-34119312803 / 1000000000000), orderedInterval (2350507055 / 1000000000000) (2350508612 / 1000000000000)))) (orderedInterval (79415243 / 1000000000000) (79415339 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks0_1 :
    compactCertificate502.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3340685558384253 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7974010856 / 1000000000000) (7974010857 / 1000000000000), orderedInterval (26427738189 / 1000000000000) (26427738190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1928745706410837 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26903820044 / 1000000000000) (-26903800145 / 1000000000000), orderedInterval (24450462656 / 1000000000000) (24450482555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3422593102279833 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25627360893 / 1000000000000) (25627472385 / 1000000000000), orderedInterval (-9356109134 / 1000000000000) (-9355997641 / 1000000000000)))) (orderedInterval (232843148 / 1000000000000) (232860620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3197830443250077 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21445754187 / 1000000000000) (21445759585 / 1000000000000), orderedInterval (-18354464687 / 1000000000000) (-18354459290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2282122696087341 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14650150013 / 1000000000000) (-14650149849 / 1000000000000), orderedInterval (30033020694 / 1000000000000) (30033020858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2587683906507339 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16077153202 / 1000000000000) (16077153203 / 1000000000000), orderedInterval (26924571881 / 1000000000000) (26924571882 / 1000000000000)))) (orderedInterval (-1853881993 / 1000000000000) (-1853881835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2157341061636891 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7949726998 / 1000000000000) (-7949726990 / 1000000000000), orderedInterval (33431625068 / 1000000000000) (33431625076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1906076253546711 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7901029249 / 1000000000000) (-7901029239 / 1000000000000), orderedInterval (35695179470 / 1000000000000) (35695179480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (552455191168389 / 800000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6145780164 / 1000000000000) (6145780165 / 1000000000000), orderedInterval (29729483001 / 1000000000000) (29729483002 / 1000000000000)))) (orderedInterval (517705054 / 1000000000000) (517705091 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks0_2 :
    compactCertificate502.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1528120132895583 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18093433204 / 1000000000000) (-18093432597 / 1000000000000), orderedInterval (36616595503 / 1000000000000) (36616596109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1295404360122663 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38504355380 / 1000000000000) (-38504355379 / 1000000000000), orderedInterval (-21922197950 / 1000000000000) (-21922197949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (810603901011789 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38927416561 / 1000000000000) (38927456440 / 1000000000000), orderedInterval (-40421170101 / 1000000000000) (-40421130221 / 1000000000000)))) (orderedInterval (6339640491 / 1000000000000) (6339641980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (435945473910963 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14067888291 / 1000000000000) (14067888391 / 1000000000000), orderedInterval (-75187309180 / 1000000000000) (-75187309080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1183676765141889 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45663125068 / 1000000000000) (45663125078 / 1000000000000), orderedInterval (8059547474 / 1000000000000) (8059547484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1616209427161953 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16475174395 / 1000000000000) (16475174750 / 1000000000000), orderedInterval (-36133497920 / 1000000000000) (-36133497564 / 1000000000000)))) (orderedInterval (-2558357021 / 1000000000000) (-2558356946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (683396098988211 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55814399425 / 1000000000000) (55814408139 / 1000000000000), orderedInterval (-24880832521 / 1000000000000) (-24880823808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2777967201370131 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25229311741 / 1000000000000) (-25229311740 / 1000000000000), orderedInterval (-16719568934 / 1000000000000) (-16719568933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1855553348226429 / 4000000000000) 0 (IntervalRat.scale (747 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10317652222 / 1000000000000) (-10317652191 / 1000000000000), orderedInterval (35590642435 / 1000000000000) (35590642466 / 1000000000000)))) (orderedInterval (4326043511 / 1000000000000) (4326043673 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks0 :
    compactCertificate502.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate502.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate502_chunkChecks0_0
    compactCertificate502_chunkChecks0_1 compactCertificate502_chunkChecks0_2

theorem compactCertificate502_chunkChecks1_0 :
    compactCertificate502.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (747 / 2) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17418149279 / 1000000000000) (-17418149278 / 1000000000000), orderedInterval (-37407681331 / 1000000000000) (-37407681330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1100473638082047 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25421561968 / 1000000000000) (-25421558471 / 1000000000000), orderedInterval (40884056543 / 1000000000000) (40884060040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (355870563897951 / 800000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17564259915 / 1000000000000) (-17564259367 / 1000000000000), orderedInterval (33525321574 / 1000000000000) (33525322122 / 1000000000000)))) (orderedInterval (-12203424269 / 1000000000000) (-12203424177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (321115462972029 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51647230648 / 1000000000000) (-51647212968 / 1000000000000), orderedInterval (72866251866 / 1000000000000) (72866269546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2342021727458421 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30577902943 / 1000000000000) (30577949108 / 1000000000000), orderedInterval (-12366703591 / 1000000000000) (-12366657426 / 1000000000000)))) (orderedInterval (129361366 / 1000000000000) (129366612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1725122604338973 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38240477909 / 1000000000000) (-38240476790 / 1000000000000), orderedInterval (3756443520 / 1000000000000) (3756444638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2956026986307729 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29309161323 / 1000000000000) (-29309160122 / 1000000000000), orderedInterval (-1537784919 / 1000000000000) (-1537783717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2177396098988211 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34119314359 / 1000000000000) (-34119312803 / 1000000000000), orderedInterval (2350507055 / 1000000000000) (2350508612 / 1000000000000)))) (orderedInterval (176639943 / 1000000000000) (176640108 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks1_1 :
    compactCertificate502.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3340685558384253 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7974010856 / 1000000000000) (7974010857 / 1000000000000), orderedInterval (26427738189 / 1000000000000) (26427738190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1928745706410837 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26903820044 / 1000000000000) (-26903800145 / 1000000000000), orderedInterval (24450462656 / 1000000000000) (24450482555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3422593102279833 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25627360893 / 1000000000000) (25627472385 / 1000000000000), orderedInterval (-9356109134 / 1000000000000) (-9355997641 / 1000000000000)))) (orderedInterval (-11208538555 / 1000000000000) (-11208500035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3197830443250077 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21445754187 / 1000000000000) (21445759585 / 1000000000000), orderedInterval (-18354464687 / 1000000000000) (-18354459290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2282122696087341 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14650150013 / 1000000000000) (-14650149849 / 1000000000000), orderedInterval (30033020694 / 1000000000000) (30033020858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2587683906507339 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16077153202 / 1000000000000) (16077153203 / 1000000000000), orderedInterval (26924571881 / 1000000000000) (26924571882 / 1000000000000)))) (orderedInterval (4811433656 / 1000000000000) (4811433961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2157341061636891 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7949726998 / 1000000000000) (-7949726990 / 1000000000000), orderedInterval (33431625068 / 1000000000000) (33431625076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1906076253546711 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7901029249 / 1000000000000) (-7901029239 / 1000000000000), orderedInterval (35695179470 / 1000000000000) (35695179480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (552455191168389 / 800000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6145780164 / 1000000000000) (6145780165 / 1000000000000), orderedInterval (29729483001 / 1000000000000) (29729483002 / 1000000000000)))) (orderedInterval (-641293935 / 1000000000000) (-641293882 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks1_2 :
    compactCertificate502.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1528120132895583 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18093433204 / 1000000000000) (-18093432597 / 1000000000000), orderedInterval (36616595503 / 1000000000000) (36616596109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1295404360122663 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38504355380 / 1000000000000) (-38504355379 / 1000000000000), orderedInterval (-21922197950 / 1000000000000) (-21922197949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (810603901011789 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38927416561 / 1000000000000) (38927456440 / 1000000000000), orderedInterval (-40421170101 / 1000000000000) (-40421130221 / 1000000000000)))) (orderedInterval (-5626553375 / 1000000000000) (-5626552484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (435945473910963 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14067888291 / 1000000000000) (14067888391 / 1000000000000), orderedInterval (-75187309180 / 1000000000000) (-75187309080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1183676765141889 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45663125068 / 1000000000000) (45663125078 / 1000000000000), orderedInterval (8059547474 / 1000000000000) (8059547484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1616209427161953 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16475174395 / 1000000000000) (16475174750 / 1000000000000), orderedInterval (-36133497920 / 1000000000000) (-36133497564 / 1000000000000)))) (orderedInterval (3256002357 / 1000000000000) (3256002428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (683396098988211 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55814399425 / 1000000000000) (55814408139 / 1000000000000), orderedInterval (-24880832521 / 1000000000000) (-24880823808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2777967201370131 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25229311741 / 1000000000000) (-25229311740 / 1000000000000), orderedInterval (-16719568934 / 1000000000000) (-16719568933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1855553348226429 / 4000000000000) 1 (IntervalRat.scale (747 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10317652222 / 1000000000000) (-10317652191 / 1000000000000), orderedInterval (35590642435 / 1000000000000) (35590642466 / 1000000000000)))) (orderedInterval (-5831727422 / 1000000000000) (-5831727245 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks1 :
    compactCertificate502.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate502.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate502_chunkChecks1_0
    compactCertificate502_chunkChecks1_1 compactCertificate502_chunkChecks1_2

theorem compactCertificate502_chunkChecks2_0 :
    compactCertificate502.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (747 / 2) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17418149279 / 1000000000000) (-17418149278 / 1000000000000), orderedInterval (-37407681331 / 1000000000000) (-37407681330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1100473638082047 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25421561968 / 1000000000000) (-25421558471 / 1000000000000), orderedInterval (40884056543 / 1000000000000) (40884060040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (355870563897951 / 800000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17564259915 / 1000000000000) (-17564259367 / 1000000000000), orderedInterval (33525321574 / 1000000000000) (33525322122 / 1000000000000)))) (orderedInterval (8527155534 / 1000000000000) (8527155632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (321115462972029 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51647230648 / 1000000000000) (-51647212968 / 1000000000000), orderedInterval (72866251866 / 1000000000000) (72866269546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2342021727458421 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30577902943 / 1000000000000) (30577949108 / 1000000000000), orderedInterval (-12366703591 / 1000000000000) (-12366657426 / 1000000000000)))) (orderedInterval (5092167154 / 1000000000000) (5092175318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1725122604338973 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38240477909 / 1000000000000) (-38240476790 / 1000000000000), orderedInterval (3756443520 / 1000000000000) (3756444638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2956026986307729 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29309161323 / 1000000000000) (-29309160122 / 1000000000000), orderedInterval (-1537784919 / 1000000000000) (-1537783717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2177396098988211 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34119314359 / 1000000000000) (-34119312803 / 1000000000000), orderedInterval (2350507055 / 1000000000000) (2350508612 / 1000000000000)))) (orderedInterval (-1788027140 / 1000000000000) (-1788026850 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks2_1 :
    compactCertificate502.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3340685558384253 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7974010856 / 1000000000000) (7974010857 / 1000000000000), orderedInterval (26427738189 / 1000000000000) (26427738190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1928745706410837 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26903820044 / 1000000000000) (-26903800145 / 1000000000000), orderedInterval (24450462656 / 1000000000000) (24450482555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3422593102279833 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25627360893 / 1000000000000) (25627472385 / 1000000000000), orderedInterval (-9356109134 / 1000000000000) (-9355997641 / 1000000000000)))) (orderedInterval (-8682965469 / 1000000000000) (-8682879071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3197830443250077 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21445754187 / 1000000000000) (21445759585 / 1000000000000), orderedInterval (-18354464687 / 1000000000000) (-18354459290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2282122696087341 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14650150013 / 1000000000000) (-14650149849 / 1000000000000), orderedInterval (30033020694 / 1000000000000) (30033020858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2587683906507339 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16077153202 / 1000000000000) (16077153203 / 1000000000000), orderedInterval (26924571881 / 1000000000000) (26924571882 / 1000000000000)))) (orderedInterval (5237494914 / 1000000000000) (5237495517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2157341061636891 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7949726998 / 1000000000000) (-7949726990 / 1000000000000), orderedInterval (33431625068 / 1000000000000) (33431625076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1906076253546711 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7901029249 / 1000000000000) (-7901029239 / 1000000000000), orderedInterval (35695179470 / 1000000000000) (35695179480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (552455191168389 / 800000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6145780164 / 1000000000000) (6145780165 / 1000000000000), orderedInterval (29729483001 / 1000000000000) (29729483002 / 1000000000000)))) (orderedInterval (-1080756429 / 1000000000000) (-1080756350 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks2_2 :
    compactCertificate502.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1528120132895583 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18093433204 / 1000000000000) (-18093432597 / 1000000000000), orderedInterval (36616595503 / 1000000000000) (36616596109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1295404360122663 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38504355380 / 1000000000000) (-38504355379 / 1000000000000), orderedInterval (-21922197950 / 1000000000000) (-21922197949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (810603901011789 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38927416561 / 1000000000000) (38927456440 / 1000000000000), orderedInterval (-40421170101 / 1000000000000) (-40421130221 / 1000000000000)))) (orderedInterval (-5023120551 / 1000000000000) (-5023119982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (435945473910963 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14067888291 / 1000000000000) (14067888391 / 1000000000000), orderedInterval (-75187309180 / 1000000000000) (-75187309080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1183676765141889 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45663125068 / 1000000000000) (45663125078 / 1000000000000), orderedInterval (8059547474 / 1000000000000) (8059547484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1616209427161953 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16475174395 / 1000000000000) (16475174750 / 1000000000000), orderedInterval (-36133497920 / 1000000000000) (-36133497564 / 1000000000000)))) (orderedInterval (2141342888 / 1000000000000) (2141342960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (683396098988211 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55814399425 / 1000000000000) (55814408139 / 1000000000000), orderedInterval (-24880832521 / 1000000000000) (-24880823808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2777967201370131 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25229311741 / 1000000000000) (-25229311740 / 1000000000000), orderedInterval (-16719568934 / 1000000000000) (-16719568933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1855553348226429 / 4000000000000) 2 (IntervalRat.scale (747 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10317652222 / 1000000000000) (-10317652191 / 1000000000000), orderedInterval (35590642435 / 1000000000000) (35590642466 / 1000000000000)))) (orderedInterval (-10141557386 / 1000000000000) (-10141557151 / 1000000000000))) = true
  rfl'

theorem compactCertificate502_chunkChecks2 :
    compactCertificate502.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate502.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate502_chunkChecks2_0
    compactCertificate502_chunkChecks2_1 compactCertificate502_chunkChecks2_2

theorem compactCertificate502_chunkChecks3_0 :
    compactCertificate502.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (747 / 2) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17418149279 / 1000000000000) (-17418149278 / 1000000000000), orderedInterval (-37407681331 / 1000000000000) (-37407681330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1100473638082047 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25421561968 / 1000000000000) (-25421558471 / 1000000000000), orderedInterval (40884056543 / 1000000000000) (40884060040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (355870563897951 / 800000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17564259915 / 1000000000000) (-17564259367 / 1000000000000), orderedInterval (33525321574 / 1000000000000) (33525322122 / 1000000000000)))) (orderedInterval (11328345814 / 1000000000000) (11328345921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (321115462972029 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51647230648 / 1000000000000) (-51647212968 / 1000000000000), orderedInterval (72866251866 / 1000000000000) (72866269546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2342021727458421 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30577902943 / 1000000000000) (30577949108 / 1000000000000), orderedInterval (-12366703591 / 1000000000000) (-12366657426 / 1000000000000)))) (orderedInterval (-3032891885 / 1000000000000) (-3032879110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1725122604338973 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38240477909 / 1000000000000) (-38240476790 / 1000000000000), orderedInterval (3756443520 / 1000000000000) (3756444638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2956026986307729 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29309161323 / 1000000000000) (-29309160122 / 1000000000000), orderedInterval (-1537784919 / 1000000000000) (-1537783717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2177396098988211 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34119314359 / 1000000000000) (-34119312803 / 1000000000000), orderedInterval (2350507055 / 1000000000000) (2350508612 / 1000000000000)))) (orderedInterval (-538470618 / 1000000000000) (-538470096 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate502_chunkChecks3_1 :
    compactCertificate502.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3340685558384253 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7974010856 / 1000000000000) (7974010857 / 1000000000000), orderedInterval (26427738189 / 1000000000000) (26427738190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1928745706410837 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26903820044 / 1000000000000) (-26903800145 / 1000000000000), orderedInterval (24450462656 / 1000000000000) (24450482555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3422593102279833 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25627360893 / 1000000000000) (25627472385 / 1000000000000), orderedInterval (-9356109134 / 1000000000000) (-9355997641 / 1000000000000)))) (orderedInterval (64617669521 / 1000000000000) (64617864923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3197830443250077 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21445754187 / 1000000000000) (21445759585 / 1000000000000), orderedInterval (-18354464687 / 1000000000000) (-18354459290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2282122696087341 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14650150013 / 1000000000000) (-14650149849 / 1000000000000), orderedInterval (30033020694 / 1000000000000) (30033020858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2587683906507339 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16077153202 / 1000000000000) (16077153203 / 1000000000000), orderedInterval (26924571881 / 1000000000000) (26924571882 / 1000000000000)))) (orderedInterval (-12677857244 / 1000000000000) (-12677856029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2157341061636891 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7949726998 / 1000000000000) (-7949726990 / 1000000000000), orderedInterval (33431625068 / 1000000000000) (33431625076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1906076253546711 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7901029249 / 1000000000000) (-7901029239 / 1000000000000), orderedInterval (35695179470 / 1000000000000) (35695179480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (552455191168389 / 800000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6145780164 / 1000000000000) (6145780165 / 1000000000000), orderedInterval (29729483001 / 1000000000000) (29729483002 / 1000000000000)))) (orderedInterval (-1728543092 / 1000000000000) (-1728542971 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate502_chunkChecks3_2 :
    compactCertificate502.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1528120132895583 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18093433204 / 1000000000000) (-18093432597 / 1000000000000), orderedInterval (36616595503 / 1000000000000) (36616596109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1295404360122663 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38504355380 / 1000000000000) (-38504355379 / 1000000000000), orderedInterval (-21922197950 / 1000000000000) (-21922197949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (810603901011789 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38927416561 / 1000000000000) (38927456440 / 1000000000000), orderedInterval (-40421170101 / 1000000000000) (-40421130221 / 1000000000000)))) (orderedInterval (5679830780 / 1000000000000) (5679831173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (435945473910963 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14067888291 / 1000000000000) (14067888391 / 1000000000000), orderedInterval (-75187309180 / 1000000000000) (-75187309080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1183676765141889 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45663125068 / 1000000000000) (45663125078 / 1000000000000), orderedInterval (8059547474 / 1000000000000) (8059547484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1616209427161953 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16475174395 / 1000000000000) (16475174750 / 1000000000000), orderedInterval (-36133497920 / 1000000000000) (-36133497564 / 1000000000000)))) (orderedInterval (-3455173908 / 1000000000000) (-3455173832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (683396098988211 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55814399425 / 1000000000000) (55814408139 / 1000000000000), orderedInterval (-24880832521 / 1000000000000) (-24880823808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2777967201370131 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25229311741 / 1000000000000) (-25229311740 / 1000000000000), orderedInterval (-16719568934 / 1000000000000) (-16719568933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1855553348226429 / 4000000000000) 3 (IntervalRat.scale (747 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10317652222 / 1000000000000) (-10317652191 / 1000000000000), orderedInterval (35590642435 / 1000000000000) (35590642466 / 1000000000000)))) (orderedInterval (4085632402 / 1000000000000) (4085632750 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate502_chunkChecks3 :
    compactCertificate502.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate502.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate502_chunkChecks3_0
    compactCertificate502_chunkChecks3_1 compactCertificate502_chunkChecks3_2

theorem compactCertificate502_chunkChecks4_0 :
    compactCertificate502.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (747 / 2) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17418149279 / 1000000000000) (-17418149278 / 1000000000000), orderedInterval (-37407681331 / 1000000000000) (-37407681330 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1100473638082047 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25421561968 / 1000000000000) (-25421558471 / 1000000000000), orderedInterval (40884056543 / 1000000000000) (40884060040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (355870563897951 / 800000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17564259915 / 1000000000000) (-17564259367 / 1000000000000), orderedInterval (33525321574 / 1000000000000) (33525322122 / 1000000000000)))) (orderedInterval (-9108113096 / 1000000000000) (-9108112975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (321115462972029 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-51647230648 / 1000000000000) (-51647212968 / 1000000000000), orderedInterval (72866251866 / 1000000000000) (72866269546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (862561302169113 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (18362864832 / 1000000000000) (18362865247 / 1000000000000), orderedInterval (-51180049130 / 1000000000000) (-51180048715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2342021727458421 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30577902943 / 1000000000000) (30577949108 / 1000000000000), orderedInterval (-12366703591 / 1000000000000) (-12366657426 / 1000000000000)))) (orderedInterval (-13035348523 / 1000000000000) (-13035328471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1725122604338973 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38240477909 / 1000000000000) (-38240476790 / 1000000000000), orderedInterval (3756443520 / 1000000000000) (3756444638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2956026986307729 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-29309161323 / 1000000000000) (-29309160122 / 1000000000000), orderedInterval (-1537784919 / 1000000000000) (-1537783717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2177396098988211 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34119314359 / 1000000000000) (-34119312803 / 1000000000000), orderedInterval (2350507055 / 1000000000000) (2350508612 / 1000000000000)))) (orderedInterval (10137436856 / 1000000000000) (10137437814 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate502_chunkChecks4_1 :
    compactCertificate502.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3340685558384253 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7974010856 / 1000000000000) (7974010857 / 1000000000000), orderedInterval (26427738189 / 1000000000000) (26427738190 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1928745706410837 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26903820044 / 1000000000000) (-26903800145 / 1000000000000), orderedInterval (24450462656 / 1000000000000) (24450482555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3422593102279833 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25627360893 / 1000000000000) (25627472385 / 1000000000000), orderedInterval (-9356109134 / 1000000000000) (-9355997641 / 1000000000000)))) (orderedInterval (59037782992 / 1000000000000) (59038227871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3197830443250077 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21445754187 / 1000000000000) (21445759585 / 1000000000000), orderedInterval (-18354464687 / 1000000000000) (-18354459290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2282122696087341 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14650150013 / 1000000000000) (-14650149849 / 1000000000000), orderedInterval (30033020694 / 1000000000000) (30033020858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2587683906507339 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16077153202 / 1000000000000) (16077153203 / 1000000000000), orderedInterval (26924571881 / 1000000000000) (26924571882 / 1000000000000)))) (orderedInterval (-16333491858 / 1000000000000) (-16333489371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2157341061636891 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7949726998 / 1000000000000) (-7949726990 / 1000000000000), orderedInterval (33431625068 / 1000000000000) (33431625076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1906076253546711 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-7901029249 / 1000000000000) (-7901029239 / 1000000000000), orderedInterval (35695179470 / 1000000000000) (35695179480 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (552455191168389 / 800000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6145780164 / 1000000000000) (6145780165 / 1000000000000), orderedInterval (29729483001 / 1000000000000) (29729483002 / 1000000000000)))) (orderedInterval (2646934542 / 1000000000000) (2646934732 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate502_chunkChecks4_2 :
    compactCertificate502.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1528120132895583 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-18093433204 / 1000000000000) (-18093432597 / 1000000000000), orderedInterval (36616595503 / 1000000000000) (36616596109 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1295404360122663 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38504355380 / 1000000000000) (-38504355379 / 1000000000000), orderedInterval (-21922197950 / 1000000000000) (-21922197949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (810603901011789 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (38927416561 / 1000000000000) (38927456440 / 1000000000000), orderedInterval (-40421170101 / 1000000000000) (-40421130221 / 1000000000000)))) (orderedInterval (4477668765 / 1000000000000) (4477669065 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (435945473910963 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (14067888291 / 1000000000000) (14067888391 / 1000000000000), orderedInterval (-75187309180 / 1000000000000) (-75187309080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1183676765141889 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45663125068 / 1000000000000) (45663125078 / 1000000000000), orderedInterval (8059547474 / 1000000000000) (8059547484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1616209427161953 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16475174395 / 1000000000000) (16475174750 / 1000000000000), orderedInterval (-36133497920 / 1000000000000) (-36133497564 / 1000000000000)))) (orderedInterval (-2120851502 / 1000000000000) (-2120851421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (683396098988211 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55814399425 / 1000000000000) (55814408139 / 1000000000000), orderedInterval (-24880832521 / 1000000000000) (-24880823808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2777967201370131 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25229311741 / 1000000000000) (-25229311740 / 1000000000000), orderedInterval (-16719568934 / 1000000000000) (-16719568933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1855553348226429 / 4000000000000) 4 (IntervalRat.scale (747 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10317652222 / 1000000000000) (-10317652191 / 1000000000000), orderedInterval (35590642435 / 1000000000000) (35590642466 / 1000000000000)))) (orderedInterval (29148884949 / 1000000000000) (29148885498 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate502_chunkChecks4 :
    compactCertificate502.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate502.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate502_chunkChecks4_0
    compactCertificate502_chunkChecks4_1 compactCertificate502_chunkChecks4_2

theorem compactCertificate502_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate502.chunkCheck r b = true :=
  compactCertificate502.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate502_chunkChecks0
    · exact compactCertificate502_chunkChecks1
    · exact compactCertificate502_chunkChecks2
    · exact compactCertificate502_chunkChecks3
    · exact compactCertificate502_chunkChecks4)

theorem compactCertificate502_coefficient0 :
    compactCertificate502.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate502_coefficient1 :
    compactCertificate502.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate502_coefficient2 :
    compactCertificate502.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate502_coefficient3 :
    compactCertificate502.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate502_coefficient4 :
    compactCertificate502.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate502_coefficients : ∀ r : Fin 5,
    compactCertificate502.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate502_coefficient0
  · exact compactCertificate502_coefficient1
  · exact compactCertificate502_coefficient2
  · exact compactCertificate502_coefficient3
  · exact compactCertificate502_coefficient4

theorem compactCertificate502_lower : (1 : ℚ) ≤ compactCertificate502.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate502, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate502_proves {t : ℝ} (ht : t ∈ compactCertificate502.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate502.proves compactCertificate502_states compactCertificate502_chunks
    compactCertificate502_coefficients compactCertificate502_lower ht

end Erdos232
