/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate598 : CompactCertificate where
  left := 469
  right := 470
  center := 939 / 2
  grid := fun i =>
    match i.val with
    | 0 => 150
    | 1 => 110
    | 2 => 178
    | 3 => 32
    | 4 => 86
    | 5 => 234
    | 6 => 173
    | 7 => 296
    | 8 => 218
    | 9 => 334
    | 10 => 193
    | 11 => 343
    | 12 => 320
    | 13 => 228
    | 14 => 259
    | 15 => 216
    | 16 => 191
    | 17 => 276
    | 18 => 153
    | 19 => 130
    | 20 => 81
    | 21 => 44
    | 22 => 118
    | 23 => 162
    | 24 => 68
    | 25 => 278
    | _ => 186
  point := fun i =>
    match i.val with
    | 0 => 939 / 2
    | 1 => 1383326300079039 / 4000000000000
    | 2 => 447339303213087 / 800000000000
    | 3 => 403651164298173 / 4000000000000
    | 4 => 1084263805537881 / 4000000000000
    | 5 => 2943987151383477 / 4000000000000
    | 6 => 2168527611076701 / 4000000000000
    | 7 => 3715809022949073 / 4000000000000
    | 8 => 2737048108366707 / 4000000000000
    | 9 => 4199335661744061 / 4000000000000
    | 10 => 2424487574725269 / 4000000000000
    | 11 => 4302295747042521 / 4000000000000
    | 12 => 4019762766013149 / 4000000000000
    | 13 => 2868692385041517 / 4000000000000
    | 14 => 3252791416613643 / 4000000000000
    | 15 => 2711838362619867 / 4000000000000
    | 16 => 2395991435181207 / 4000000000000
    | 17 => 694451706167493 / 800000000000
    | 18 => 1920889966250271 / 4000000000000
    | 19 => 1628359697664231 / 4000000000000
    | 20 => 1018951891633293 / 4000000000000
    | 21 => 547995716201331 / 4000000000000
    | 22 => 1487914969836993 / 4000000000000
    | 23 => 2031620685548961 / 4000000000000
    | 24 => 859048108366707 / 4000000000000
    | 25 => 3491982867585747 / 4000000000000
    | _ => 2332482722870973 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-30033089895 / 1000000000000) (-30033027386 / 1000000000000), orderedInterval (21338470775 / 1000000000000) (21338533284 / 1000000000000))
    | 1 => (orderedInterval (37032220639 / 1000000000000) (37032220640 / 1000000000000), orderedInterval (21613284350 / 1000000000000) (21613284351 / 1000000000000))
    | 2 => (orderedInterval (23142705449 / 1000000000000) (23142705450 / 1000000000000), orderedInterval (24533639158 / 1000000000000) (24533639159 / 1000000000000))
    | 3 => (orderedInterval (73006820249 / 1000000000000) (73006820250 / 1000000000000), orderedInterval (30920285149 / 1000000000000) (30920285150 / 1000000000000))
    | 4 => (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))
    | 5 => (orderedInterval (29319812704 / 1000000000000) (29319817794 / 1000000000000), orderedInterval (-2327414092 / 1000000000000) (-2327409003 / 1000000000000))
    | 6 => (orderedInterval (18735427219 / 1000000000000) (18735428182 / 1000000000000), orderedInterval (-28710021038 / 1000000000000) (-28710020074 / 1000000000000))
    | 7 => (orderedInterval (-4529673583 / 1000000000000) (-4529673582 / 1000000000000), orderedInterval (25785991231 / 1000000000000) (25785991232 / 1000000000000))
    | 8 => (orderedInterval (5462089146 / 1000000000000) (5462089147 / 1000000000000), orderedInterval (30005008554 / 1000000000000) (30005008555 / 1000000000000))
    | 9 => (orderedInterval (23898470702 / 1000000000000) (23898471515 / 1000000000000), orderedInterval (5926923768 / 1000000000000) (5926924580 / 1000000000000))
    | 10 => (orderedInterval (-17752638368 / 1000000000000) (-17752638367 / 1000000000000), orderedInterval (-27099196781 / 1000000000000) (-27099196780 / 1000000000000))
    | 11 => (orderedInterval (22737017712 / 1000000000000) (22737056544 / 1000000000000), orderedInterval (-8665963531 / 1000000000000) (-8665924699 / 1000000000000))
    | 12 => (orderedInterval (10178282881 / 1000000000000) (10178282882 / 1000000000000), orderedInterval (23014329976 / 1000000000000) (23014329977 / 1000000000000))
    | 13 => (orderedInterval (29631725800 / 1000000000000) (29631731834 / 1000000000000), orderedInterval (-3125466929 / 1000000000000) (-3125460895 / 1000000000000))
    | 14 => (orderedInterval (-8551447895 / 1000000000000) (-8551447894 / 1000000000000), orderedInterval (-26635547081 / 1000000000000) (-26635547080 / 1000000000000))
    | 15 => (orderedInterval (4906000359 / 1000000000000) (4906000360 / 1000000000000), orderedInterval (30244598023 / 1000000000000) (30244598024 / 1000000000000))
    | 16 => (orderedInterval (8417193981 / 1000000000000) (8417193988 / 1000000000000), orderedInterval (-31502410802 / 1000000000000) (-31502410795 / 1000000000000))
    | 17 => (orderedInterval (26543712973 / 1000000000000) (26543744955 / 1000000000000), orderedInterval (-5382671863 / 1000000000000) (-5382639881 / 1000000000000))
    | 18 => (orderedInterval (-12277817994 / 1000000000000) (-12277817993 / 1000000000000), orderedInterval (-34264504213 / 1000000000000) (-34264504212 / 1000000000000))
    | 19 => (orderedInterval (-20060664475 / 1000000000000) (-20060663225 / 1000000000000), orderedInterval (34103974731 / 1000000000000) (34103975980 / 1000000000000))
    | 20 => (orderedInterval (-43459523971 / 1000000000000) (-43459523970 / 1000000000000), orderedInterval (-24620636998 / 1000000000000) (-24620636997 / 1000000000000))
    | 21 => (orderedInterval (-29445635273 / 1000000000000) (-29445633034 / 1000000000000), orderedInterval (61588111432 / 1000000000000) (61588113671 / 1000000000000))
    | 22 => (orderedInterval (36597133573 / 1000000000000) (36597177072 / 1000000000000), orderedInterval (-19338811104 / 1000000000000) (-19338767605 / 1000000000000))
    | 23 => (orderedInterval (-8679629658 / 1000000000000) (-8679629646 / 1000000000000), orderedInterval (34331817513 / 1000000000000) (34331817525 / 1000000000000))
    | 24 => (orderedInterval (51186407326 / 1000000000000) (51186412703 / 1000000000000), orderedInterval (-18673106629 / 1000000000000) (-18673101252 / 1000000000000))
    | 25 => (orderedInterval (10967260838 / 1000000000000) (10967260839 / 1000000000000), orderedInterval (24670734601 / 1000000000000) (24670734602 / 1000000000000))
    | _ => (orderedInterval (-13785151520 / 1000000000000) (-13785151412 / 1000000000000), orderedInterval (30040407053 / 1000000000000) (30040407161 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-10200956690 / 1000000000000) (-10200931881 / 1000000000000)
      | 1 => orderedInterval (-1116372026 / 1000000000000) (-1116371591 / 1000000000000)
      | 2 => orderedInterval (271721161 / 1000000000000) (271721188 / 1000000000000)
      | 3 => orderedInterval (-2329593313 / 1000000000000) (-2329587463 / 1000000000000)
      | 4 => orderedInterval (2661586724 / 1000000000000) (2661587351 / 1000000000000)
      | 5 => orderedInterval (254588709 / 1000000000000) (254589573 / 1000000000000)
      | 6 => orderedInterval (1683726318 / 1000000000000) (1683726507 / 1000000000000)
      | 7 => orderedInterval (378638933 / 1000000000000) (378640019 / 1000000000000)
      | _ => orderedInterval (2002273950 / 1000000000000) (2002274133 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (10320804824 / 1000000000000) (10320829637 / 1000000000000)
      | 1 => orderedInterval (80228734 / 1000000000000) (80229375 / 1000000000000)
      | 2 => orderedInterval (-516794658 / 1000000000000) (-516794612 / 1000000000000)
      | 3 => orderedInterval (-7769184473 / 1000000000000) (-7769171119 / 1000000000000)
      | 4 => orderedInterval (-1107312615 / 1000000000000) (-1107311653 / 1000000000000)
      | 5 => orderedInterval (2549533998 / 1000000000000) (2549535578 / 1000000000000)
      | 6 => orderedInterval (3495174341 / 1000000000000) (3495174512 / 1000000000000)
      | 7 => orderedInterval (-2830616928 / 1000000000000) (-2830616083 / 1000000000000)
      | _ => orderedInterval (-10786048533 / 1000000000000) (-10786048310 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9768481420 / 1000000000000) (9768506292 / 1000000000000)
      | 1 => orderedInterval (4571843768 / 1000000000000) (4571844753 / 1000000000000)
      | 2 => orderedInterval (-826253535 / 1000000000000) (-826253453 / 1000000000000)
      | 3 => orderedInterval (6477876977 / 1000000000000) (6477907524 / 1000000000000)
      | 4 => orderedInterval (-5823759022 / 1000000000000) (-5823757538 / 1000000000000)
      | 5 => orderedInterval (-1662790157 / 1000000000000) (-1662787256 / 1000000000000)
      | 6 => orderedInterval (-2498392414 / 1000000000000) (-2498392256 / 1000000000000)
      | 7 => orderedInterval (-297562123 / 1000000000000) (-297561447 / 1000000000000)
      | _ => orderedInterval (-944760951 / 1000000000000) (-944760643 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10991271058 / 1000000000000) (-10991246179 / 1000000000000)
      | 1 => orderedInterval (-608110854 / 1000000000000) (-608109323 / 1000000000000)
      | 2 => orderedInterval (3917535064 / 1000000000000) (3917535212 / 1000000000000)
      | 3 => orderedInterval (30892138686 / 1000000000000) (30892208543 / 1000000000000)
      | 4 => orderedInterval (4439825158 / 1000000000000) (4439827449 / 1000000000000)
      | 5 => orderedInterval (-3920759313 / 1000000000000) (-3920753981 / 1000000000000)
      | 6 => orderedInterval (-4470972525 / 1000000000000) (-4470972378 / 1000000000000)
      | 7 => orderedInterval (3141772179 / 1000000000000) (3141772725 / 1000000000000)
      | _ => orderedInterval (23721938512 / 1000000000000) (23721938971 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9023127225 / 1000000000000) (-9023102285 / 1000000000000)
      | 1 => orderedInterval (-12390712468 / 1000000000000) (-12390710070 / 1000000000000)
      | 2 => orderedInterval (2720154983 / 1000000000000) (2720155258 / 1000000000000)
      | 3 => orderedInterval (-20920953177 / 1000000000000) (-20920793209 / 1000000000000)
      | 4 => orderedInterval (11769241079 / 1000000000000) (11769244637 / 1000000000000)
      | 5 => orderedInterval (6928878813 / 1000000000000) (6928888641 / 1000000000000)
      | 6 => orderedInterval (2686896796 / 1000000000000) (2686896936 / 1000000000000)
      | 7 => orderedInterval (574445183 / 1000000000000) (574445630 / 1000000000000)
      | _ => orderedInterval (-4604795626 / 1000000000000) (-4604794908 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-6394386234 / 1000000000000) (-6394352164 / 1000000000000)
    | 1 => orderedInterval (-6564215310 / 1000000000000) (-6564172675 / 1000000000000)
    | 2 => orderedInterval (8764683963 / 1000000000000) (8764745976 / 1000000000000)
    | 3 => orderedInterval (46122095849 / 1000000000000) (46122201039 / 1000000000000)
    | _ => orderedInterval (-22259971642 / 1000000000000) (-22259769370 / 1000000000000)

theorem compactCertificate598_stateChecks0 :
    compactCertificate598.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (939 / 2)) (orderedInterval (-30033089895 / 1000000000000) (-30033027386 / 1000000000000), orderedInterval (21338470775 / 1000000000000) (21338533284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1383326300079039 / 4000000000000)) (orderedInterval (37032220639 / 1000000000000) (37032220640 / 1000000000000), orderedInterval (21613284350 / 1000000000000) (21613284351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (447339303213087 / 800000000000)) (orderedInterval (23142705449 / 1000000000000) (23142705450 / 1000000000000), orderedInterval (24533639158 / 1000000000000) (24533639159 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks1 :
    compactCertificate598.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (403651164298173 / 4000000000000)) (orderedInterval (73006820249 / 1000000000000) (73006820250 / 1000000000000), orderedInterval (30920285149 / 1000000000000) (30920285150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1084263805537881 / 4000000000000)) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2943987151383477 / 4000000000000)) (orderedInterval (29319812704 / 1000000000000) (29319817794 / 1000000000000), orderedInterval (-2327414092 / 1000000000000) (-2327409003 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks2 :
    compactCertificate598.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2168527611076701 / 4000000000000)) (orderedInterval (18735427219 / 1000000000000) (18735428182 / 1000000000000), orderedInterval (-28710021038 / 1000000000000) (-28710020074 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 296 12 (3715809022949073 / 4000000000000)) (orderedInterval (-4529673583 / 1000000000000) (-4529673582 / 1000000000000), orderedInterval (25785991231 / 1000000000000) (25785991232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2737048108366707 / 4000000000000)) (orderedInterval (5462089146 / 1000000000000) (5462089147 / 1000000000000), orderedInterval (30005008554 / 1000000000000) (30005008555 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks3 :
    compactCertificate598.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 334 12 (4199335661744061 / 4000000000000)) (orderedInterval (23898470702 / 1000000000000) (23898471515 / 1000000000000), orderedInterval (5926923768 / 1000000000000) (5926924580 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2424487574725269 / 4000000000000)) (orderedInterval (-17752638368 / 1000000000000) (-17752638367 / 1000000000000), orderedInterval (-27099196781 / 1000000000000) (-27099196780 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 343 12 (4302295747042521 / 4000000000000)) (orderedInterval (22737017712 / 1000000000000) (22737056544 / 1000000000000), orderedInterval (-8665963531 / 1000000000000) (-8665924699 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks4 :
    compactCertificate598.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 320 12 (4019762766013149 / 4000000000000)) (orderedInterval (10178282881 / 1000000000000) (10178282882 / 1000000000000), orderedInterval (23014329976 / 1000000000000) (23014329977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2868692385041517 / 4000000000000)) (orderedInterval (29631725800 / 1000000000000) (29631731834 / 1000000000000), orderedInterval (-3125466929 / 1000000000000) (-3125460895 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3252791416613643 / 4000000000000)) (orderedInterval (-8551447895 / 1000000000000) (-8551447894 / 1000000000000), orderedInterval (-26635547081 / 1000000000000) (-26635547080 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks5 :
    compactCertificate598.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2711838362619867 / 4000000000000)) (orderedInterval (4906000359 / 1000000000000) (4906000360 / 1000000000000), orderedInterval (30244598023 / 1000000000000) (30244598024 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2395991435181207 / 4000000000000)) (orderedInterval (8417193981 / 1000000000000) (8417193988 / 1000000000000), orderedInterval (-31502410802 / 1000000000000) (-31502410795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (694451706167493 / 800000000000)) (orderedInterval (26543712973 / 1000000000000) (26543744955 / 1000000000000), orderedInterval (-5382671863 / 1000000000000) (-5382639881 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks6 :
    compactCertificate598.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1920889966250271 / 4000000000000)) (orderedInterval (-12277817994 / 1000000000000) (-12277817993 / 1000000000000), orderedInterval (-34264504213 / 1000000000000) (-34264504212 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1628359697664231 / 4000000000000)) (orderedInterval (-20060664475 / 1000000000000) (-20060663225 / 1000000000000), orderedInterval (34103974731 / 1000000000000) (34103975980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1018951891633293 / 4000000000000)) (orderedInterval (-43459523971 / 1000000000000) (-43459523970 / 1000000000000), orderedInterval (-24620636998 / 1000000000000) (-24620636997 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks7 :
    compactCertificate598.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (547995716201331 / 4000000000000)) (orderedInterval (-29445635273 / 1000000000000) (-29445633034 / 1000000000000), orderedInterval (61588111432 / 1000000000000) (61588113671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1487914969836993 / 4000000000000)) (orderedInterval (36597133573 / 1000000000000) (36597177072 / 1000000000000), orderedInterval (-19338811104 / 1000000000000) (-19338767605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2031620685548961 / 4000000000000)) (orderedInterval (-8679629658 / 1000000000000) (-8679629646 / 1000000000000), orderedInterval (34331817513 / 1000000000000) (34331817525 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_stateChecks8 :
    compactCertificate598.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (859048108366707 / 4000000000000)) (orderedInterval (51186407326 / 1000000000000) (51186412703 / 1000000000000), orderedInterval (-18673106629 / 1000000000000) (-18673101252 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (3491982867585747 / 4000000000000)) (orderedInterval (10967260838 / 1000000000000) (10967260839 / 1000000000000), orderedInterval (24670734601 / 1000000000000) (24670734602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2332482722870973 / 4000000000000)) (orderedInterval (-13785151520 / 1000000000000) (-13785151412 / 1000000000000), orderedInterval (30040407053 / 1000000000000) (30040407161 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_states : ∀ j,
    BesselStateValid (compactCertificate598.point j) (compactCertificate598.state j) :=
  compactCertificate598.statesValid_of_checks3 compactCertificate598_stateChecks0
    compactCertificate598_stateChecks1 compactCertificate598_stateChecks2
    compactCertificate598_stateChecks3 compactCertificate598_stateChecks4
    compactCertificate598_stateChecks5 compactCertificate598_stateChecks6
    compactCertificate598_stateChecks7 compactCertificate598_stateChecks8

theorem compactCertificate598_chunkChecks0_0 :
    compactCertificate598.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (939 / 2) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30033089895 / 1000000000000) (-30033027386 / 1000000000000), orderedInterval (21338470775 / 1000000000000) (21338533284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1383326300079039 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37032220639 / 1000000000000) (37032220640 / 1000000000000), orderedInterval (21613284350 / 1000000000000) (21613284351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (447339303213087 / 800000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23142705449 / 1000000000000) (23142705450 / 1000000000000), orderedInterval (24533639158 / 1000000000000) (24533639159 / 1000000000000)))) (orderedInterval (-10200956690 / 1000000000000) (-10200931881 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (403651164298173 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73006820249 / 1000000000000) (73006820250 / 1000000000000), orderedInterval (30920285149 / 1000000000000) (30920285150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2943987151383477 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29319812704 / 1000000000000) (29319817794 / 1000000000000), orderedInterval (-2327414092 / 1000000000000) (-2327409003 / 1000000000000)))) (orderedInterval (-1116372026 / 1000000000000) (-1116371591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2168527611076701 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18735427219 / 1000000000000) (18735428182 / 1000000000000), orderedInterval (-28710021038 / 1000000000000) (-28710020074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3715809022949073 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4529673583 / 1000000000000) (-4529673582 / 1000000000000), orderedInterval (25785991231 / 1000000000000) (25785991232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2737048108366707 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5462089146 / 1000000000000) (5462089147 / 1000000000000), orderedInterval (30005008554 / 1000000000000) (30005008555 / 1000000000000)))) (orderedInterval (271721161 / 1000000000000) (271721188 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks0_1 :
    compactCertificate598.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4199335661744061 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23898470702 / 1000000000000) (23898471515 / 1000000000000), orderedInterval (5926923768 / 1000000000000) (5926924580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2424487574725269 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17752638368 / 1000000000000) (-17752638367 / 1000000000000), orderedInterval (-27099196781 / 1000000000000) (-27099196780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4302295747042521 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22737017712 / 1000000000000) (22737056544 / 1000000000000), orderedInterval (-8665963531 / 1000000000000) (-8665924699 / 1000000000000)))) (orderedInterval (-2329593313 / 1000000000000) (-2329587463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4019762766013149 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10178282881 / 1000000000000) (10178282882 / 1000000000000), orderedInterval (23014329976 / 1000000000000) (23014329977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2868692385041517 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29631725800 / 1000000000000) (29631731834 / 1000000000000), orderedInterval (-3125466929 / 1000000000000) (-3125460895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3252791416613643 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8551447895 / 1000000000000) (-8551447894 / 1000000000000), orderedInterval (-26635547081 / 1000000000000) (-26635547080 / 1000000000000)))) (orderedInterval (2661586724 / 1000000000000) (2661587351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2711838362619867 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4906000359 / 1000000000000) (4906000360 / 1000000000000), orderedInterval (30244598023 / 1000000000000) (30244598024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2395991435181207 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8417193981 / 1000000000000) (8417193988 / 1000000000000), orderedInterval (-31502410802 / 1000000000000) (-31502410795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (694451706167493 / 800000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26543712973 / 1000000000000) (26543744955 / 1000000000000), orderedInterval (-5382671863 / 1000000000000) (-5382639881 / 1000000000000)))) (orderedInterval (254588709 / 1000000000000) (254589573 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks0_2 :
    compactCertificate598.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1920889966250271 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12277817994 / 1000000000000) (-12277817993 / 1000000000000), orderedInterval (-34264504213 / 1000000000000) (-34264504212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1628359697664231 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20060664475 / 1000000000000) (-20060663225 / 1000000000000), orderedInterval (34103974731 / 1000000000000) (34103975980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1018951891633293 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43459523971 / 1000000000000) (-43459523970 / 1000000000000), orderedInterval (-24620636998 / 1000000000000) (-24620636997 / 1000000000000)))) (orderedInterval (1683726318 / 1000000000000) (1683726507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (547995716201331 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29445635273 / 1000000000000) (-29445633034 / 1000000000000), orderedInterval (61588111432 / 1000000000000) (61588113671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1487914969836993 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36597133573 / 1000000000000) (36597177072 / 1000000000000), orderedInterval (-19338811104 / 1000000000000) (-19338767605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2031620685548961 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8679629658 / 1000000000000) (-8679629646 / 1000000000000), orderedInterval (34331817513 / 1000000000000) (34331817525 / 1000000000000)))) (orderedInterval (378638933 / 1000000000000) (378640019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (859048108366707 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51186407326 / 1000000000000) (51186412703 / 1000000000000), orderedInterval (-18673106629 / 1000000000000) (-18673101252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3491982867585747 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10967260838 / 1000000000000) (10967260839 / 1000000000000), orderedInterval (24670734601 / 1000000000000) (24670734602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2332482722870973 / 4000000000000) 0 (IntervalRat.scale (939 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13785151520 / 1000000000000) (-13785151412 / 1000000000000), orderedInterval (30040407053 / 1000000000000) (30040407161 / 1000000000000)))) (orderedInterval (2002273950 / 1000000000000) (2002274133 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks0 :
    compactCertificate598.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate598.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate598_chunkChecks0_0
    compactCertificate598_chunkChecks0_1 compactCertificate598_chunkChecks0_2

theorem compactCertificate598_chunkChecks1_0 :
    compactCertificate598.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (939 / 2) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30033089895 / 1000000000000) (-30033027386 / 1000000000000), orderedInterval (21338470775 / 1000000000000) (21338533284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1383326300079039 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37032220639 / 1000000000000) (37032220640 / 1000000000000), orderedInterval (21613284350 / 1000000000000) (21613284351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (447339303213087 / 800000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23142705449 / 1000000000000) (23142705450 / 1000000000000), orderedInterval (24533639158 / 1000000000000) (24533639159 / 1000000000000)))) (orderedInterval (10320804824 / 1000000000000) (10320829637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (403651164298173 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73006820249 / 1000000000000) (73006820250 / 1000000000000), orderedInterval (30920285149 / 1000000000000) (30920285150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2943987151383477 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29319812704 / 1000000000000) (29319817794 / 1000000000000), orderedInterval (-2327414092 / 1000000000000) (-2327409003 / 1000000000000)))) (orderedInterval (80228734 / 1000000000000) (80229375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2168527611076701 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18735427219 / 1000000000000) (18735428182 / 1000000000000), orderedInterval (-28710021038 / 1000000000000) (-28710020074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3715809022949073 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4529673583 / 1000000000000) (-4529673582 / 1000000000000), orderedInterval (25785991231 / 1000000000000) (25785991232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2737048108366707 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5462089146 / 1000000000000) (5462089147 / 1000000000000), orderedInterval (30005008554 / 1000000000000) (30005008555 / 1000000000000)))) (orderedInterval (-516794658 / 1000000000000) (-516794612 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks1_1 :
    compactCertificate598.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4199335661744061 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23898470702 / 1000000000000) (23898471515 / 1000000000000), orderedInterval (5926923768 / 1000000000000) (5926924580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2424487574725269 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17752638368 / 1000000000000) (-17752638367 / 1000000000000), orderedInterval (-27099196781 / 1000000000000) (-27099196780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4302295747042521 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22737017712 / 1000000000000) (22737056544 / 1000000000000), orderedInterval (-8665963531 / 1000000000000) (-8665924699 / 1000000000000)))) (orderedInterval (-7769184473 / 1000000000000) (-7769171119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4019762766013149 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10178282881 / 1000000000000) (10178282882 / 1000000000000), orderedInterval (23014329976 / 1000000000000) (23014329977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2868692385041517 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29631725800 / 1000000000000) (29631731834 / 1000000000000), orderedInterval (-3125466929 / 1000000000000) (-3125460895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3252791416613643 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8551447895 / 1000000000000) (-8551447894 / 1000000000000), orderedInterval (-26635547081 / 1000000000000) (-26635547080 / 1000000000000)))) (orderedInterval (-1107312615 / 1000000000000) (-1107311653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2711838362619867 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4906000359 / 1000000000000) (4906000360 / 1000000000000), orderedInterval (30244598023 / 1000000000000) (30244598024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2395991435181207 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8417193981 / 1000000000000) (8417193988 / 1000000000000), orderedInterval (-31502410802 / 1000000000000) (-31502410795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (694451706167493 / 800000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26543712973 / 1000000000000) (26543744955 / 1000000000000), orderedInterval (-5382671863 / 1000000000000) (-5382639881 / 1000000000000)))) (orderedInterval (2549533998 / 1000000000000) (2549535578 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks1_2 :
    compactCertificate598.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1920889966250271 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12277817994 / 1000000000000) (-12277817993 / 1000000000000), orderedInterval (-34264504213 / 1000000000000) (-34264504212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1628359697664231 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20060664475 / 1000000000000) (-20060663225 / 1000000000000), orderedInterval (34103974731 / 1000000000000) (34103975980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1018951891633293 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43459523971 / 1000000000000) (-43459523970 / 1000000000000), orderedInterval (-24620636998 / 1000000000000) (-24620636997 / 1000000000000)))) (orderedInterval (3495174341 / 1000000000000) (3495174512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (547995716201331 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29445635273 / 1000000000000) (-29445633034 / 1000000000000), orderedInterval (61588111432 / 1000000000000) (61588113671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1487914969836993 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36597133573 / 1000000000000) (36597177072 / 1000000000000), orderedInterval (-19338811104 / 1000000000000) (-19338767605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2031620685548961 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8679629658 / 1000000000000) (-8679629646 / 1000000000000), orderedInterval (34331817513 / 1000000000000) (34331817525 / 1000000000000)))) (orderedInterval (-2830616928 / 1000000000000) (-2830616083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (859048108366707 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51186407326 / 1000000000000) (51186412703 / 1000000000000), orderedInterval (-18673106629 / 1000000000000) (-18673101252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3491982867585747 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10967260838 / 1000000000000) (10967260839 / 1000000000000), orderedInterval (24670734601 / 1000000000000) (24670734602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2332482722870973 / 4000000000000) 1 (IntervalRat.scale (939 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13785151520 / 1000000000000) (-13785151412 / 1000000000000), orderedInterval (30040407053 / 1000000000000) (30040407161 / 1000000000000)))) (orderedInterval (-10786048533 / 1000000000000) (-10786048310 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks1 :
    compactCertificate598.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate598.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate598_chunkChecks1_0
    compactCertificate598_chunkChecks1_1 compactCertificate598_chunkChecks1_2

theorem compactCertificate598_chunkChecks2_0 :
    compactCertificate598.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (939 / 2) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30033089895 / 1000000000000) (-30033027386 / 1000000000000), orderedInterval (21338470775 / 1000000000000) (21338533284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1383326300079039 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37032220639 / 1000000000000) (37032220640 / 1000000000000), orderedInterval (21613284350 / 1000000000000) (21613284351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (447339303213087 / 800000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23142705449 / 1000000000000) (23142705450 / 1000000000000), orderedInterval (24533639158 / 1000000000000) (24533639159 / 1000000000000)))) (orderedInterval (9768481420 / 1000000000000) (9768506292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (403651164298173 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73006820249 / 1000000000000) (73006820250 / 1000000000000), orderedInterval (30920285149 / 1000000000000) (30920285150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2943987151383477 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29319812704 / 1000000000000) (29319817794 / 1000000000000), orderedInterval (-2327414092 / 1000000000000) (-2327409003 / 1000000000000)))) (orderedInterval (4571843768 / 1000000000000) (4571844753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2168527611076701 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18735427219 / 1000000000000) (18735428182 / 1000000000000), orderedInterval (-28710021038 / 1000000000000) (-28710020074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3715809022949073 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4529673583 / 1000000000000) (-4529673582 / 1000000000000), orderedInterval (25785991231 / 1000000000000) (25785991232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2737048108366707 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5462089146 / 1000000000000) (5462089147 / 1000000000000), orderedInterval (30005008554 / 1000000000000) (30005008555 / 1000000000000)))) (orderedInterval (-826253535 / 1000000000000) (-826253453 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks2_1 :
    compactCertificate598.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4199335661744061 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23898470702 / 1000000000000) (23898471515 / 1000000000000), orderedInterval (5926923768 / 1000000000000) (5926924580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2424487574725269 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17752638368 / 1000000000000) (-17752638367 / 1000000000000), orderedInterval (-27099196781 / 1000000000000) (-27099196780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4302295747042521 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22737017712 / 1000000000000) (22737056544 / 1000000000000), orderedInterval (-8665963531 / 1000000000000) (-8665924699 / 1000000000000)))) (orderedInterval (6477876977 / 1000000000000) (6477907524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4019762766013149 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10178282881 / 1000000000000) (10178282882 / 1000000000000), orderedInterval (23014329976 / 1000000000000) (23014329977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2868692385041517 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29631725800 / 1000000000000) (29631731834 / 1000000000000), orderedInterval (-3125466929 / 1000000000000) (-3125460895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3252791416613643 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8551447895 / 1000000000000) (-8551447894 / 1000000000000), orderedInterval (-26635547081 / 1000000000000) (-26635547080 / 1000000000000)))) (orderedInterval (-5823759022 / 1000000000000) (-5823757538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2711838362619867 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4906000359 / 1000000000000) (4906000360 / 1000000000000), orderedInterval (30244598023 / 1000000000000) (30244598024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2395991435181207 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8417193981 / 1000000000000) (8417193988 / 1000000000000), orderedInterval (-31502410802 / 1000000000000) (-31502410795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (694451706167493 / 800000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26543712973 / 1000000000000) (26543744955 / 1000000000000), orderedInterval (-5382671863 / 1000000000000) (-5382639881 / 1000000000000)))) (orderedInterval (-1662790157 / 1000000000000) (-1662787256 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks2_2 :
    compactCertificate598.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1920889966250271 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12277817994 / 1000000000000) (-12277817993 / 1000000000000), orderedInterval (-34264504213 / 1000000000000) (-34264504212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1628359697664231 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20060664475 / 1000000000000) (-20060663225 / 1000000000000), orderedInterval (34103974731 / 1000000000000) (34103975980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1018951891633293 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43459523971 / 1000000000000) (-43459523970 / 1000000000000), orderedInterval (-24620636998 / 1000000000000) (-24620636997 / 1000000000000)))) (orderedInterval (-2498392414 / 1000000000000) (-2498392256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (547995716201331 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29445635273 / 1000000000000) (-29445633034 / 1000000000000), orderedInterval (61588111432 / 1000000000000) (61588113671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1487914969836993 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36597133573 / 1000000000000) (36597177072 / 1000000000000), orderedInterval (-19338811104 / 1000000000000) (-19338767605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2031620685548961 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8679629658 / 1000000000000) (-8679629646 / 1000000000000), orderedInterval (34331817513 / 1000000000000) (34331817525 / 1000000000000)))) (orderedInterval (-297562123 / 1000000000000) (-297561447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (859048108366707 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51186407326 / 1000000000000) (51186412703 / 1000000000000), orderedInterval (-18673106629 / 1000000000000) (-18673101252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3491982867585747 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10967260838 / 1000000000000) (10967260839 / 1000000000000), orderedInterval (24670734601 / 1000000000000) (24670734602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2332482722870973 / 4000000000000) 2 (IntervalRat.scale (939 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13785151520 / 1000000000000) (-13785151412 / 1000000000000), orderedInterval (30040407053 / 1000000000000) (30040407161 / 1000000000000)))) (orderedInterval (-944760951 / 1000000000000) (-944760643 / 1000000000000))) = true
  rfl'

theorem compactCertificate598_chunkChecks2 :
    compactCertificate598.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate598.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate598_chunkChecks2_0
    compactCertificate598_chunkChecks2_1 compactCertificate598_chunkChecks2_2

theorem compactCertificate598_chunkChecks3_0 :
    compactCertificate598.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (939 / 2) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30033089895 / 1000000000000) (-30033027386 / 1000000000000), orderedInterval (21338470775 / 1000000000000) (21338533284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1383326300079039 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37032220639 / 1000000000000) (37032220640 / 1000000000000), orderedInterval (21613284350 / 1000000000000) (21613284351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (447339303213087 / 800000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23142705449 / 1000000000000) (23142705450 / 1000000000000), orderedInterval (24533639158 / 1000000000000) (24533639159 / 1000000000000)))) (orderedInterval (-10991271058 / 1000000000000) (-10991246179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (403651164298173 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73006820249 / 1000000000000) (73006820250 / 1000000000000), orderedInterval (30920285149 / 1000000000000) (30920285150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2943987151383477 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29319812704 / 1000000000000) (29319817794 / 1000000000000), orderedInterval (-2327414092 / 1000000000000) (-2327409003 / 1000000000000)))) (orderedInterval (-608110854 / 1000000000000) (-608109323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2168527611076701 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18735427219 / 1000000000000) (18735428182 / 1000000000000), orderedInterval (-28710021038 / 1000000000000) (-28710020074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3715809022949073 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4529673583 / 1000000000000) (-4529673582 / 1000000000000), orderedInterval (25785991231 / 1000000000000) (25785991232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2737048108366707 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5462089146 / 1000000000000) (5462089147 / 1000000000000), orderedInterval (30005008554 / 1000000000000) (30005008555 / 1000000000000)))) (orderedInterval (3917535064 / 1000000000000) (3917535212 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate598_chunkChecks3_1 :
    compactCertificate598.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4199335661744061 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23898470702 / 1000000000000) (23898471515 / 1000000000000), orderedInterval (5926923768 / 1000000000000) (5926924580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2424487574725269 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17752638368 / 1000000000000) (-17752638367 / 1000000000000), orderedInterval (-27099196781 / 1000000000000) (-27099196780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4302295747042521 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22737017712 / 1000000000000) (22737056544 / 1000000000000), orderedInterval (-8665963531 / 1000000000000) (-8665924699 / 1000000000000)))) (orderedInterval (30892138686 / 1000000000000) (30892208543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4019762766013149 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10178282881 / 1000000000000) (10178282882 / 1000000000000), orderedInterval (23014329976 / 1000000000000) (23014329977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2868692385041517 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29631725800 / 1000000000000) (29631731834 / 1000000000000), orderedInterval (-3125466929 / 1000000000000) (-3125460895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3252791416613643 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8551447895 / 1000000000000) (-8551447894 / 1000000000000), orderedInterval (-26635547081 / 1000000000000) (-26635547080 / 1000000000000)))) (orderedInterval (4439825158 / 1000000000000) (4439827449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2711838362619867 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4906000359 / 1000000000000) (4906000360 / 1000000000000), orderedInterval (30244598023 / 1000000000000) (30244598024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2395991435181207 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8417193981 / 1000000000000) (8417193988 / 1000000000000), orderedInterval (-31502410802 / 1000000000000) (-31502410795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (694451706167493 / 800000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26543712973 / 1000000000000) (26543744955 / 1000000000000), orderedInterval (-5382671863 / 1000000000000) (-5382639881 / 1000000000000)))) (orderedInterval (-3920759313 / 1000000000000) (-3920753981 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate598_chunkChecks3_2 :
    compactCertificate598.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1920889966250271 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12277817994 / 1000000000000) (-12277817993 / 1000000000000), orderedInterval (-34264504213 / 1000000000000) (-34264504212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1628359697664231 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20060664475 / 1000000000000) (-20060663225 / 1000000000000), orderedInterval (34103974731 / 1000000000000) (34103975980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1018951891633293 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43459523971 / 1000000000000) (-43459523970 / 1000000000000), orderedInterval (-24620636998 / 1000000000000) (-24620636997 / 1000000000000)))) (orderedInterval (-4470972525 / 1000000000000) (-4470972378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (547995716201331 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29445635273 / 1000000000000) (-29445633034 / 1000000000000), orderedInterval (61588111432 / 1000000000000) (61588113671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1487914969836993 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36597133573 / 1000000000000) (36597177072 / 1000000000000), orderedInterval (-19338811104 / 1000000000000) (-19338767605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2031620685548961 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8679629658 / 1000000000000) (-8679629646 / 1000000000000), orderedInterval (34331817513 / 1000000000000) (34331817525 / 1000000000000)))) (orderedInterval (3141772179 / 1000000000000) (3141772725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (859048108366707 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51186407326 / 1000000000000) (51186412703 / 1000000000000), orderedInterval (-18673106629 / 1000000000000) (-18673101252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3491982867585747 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10967260838 / 1000000000000) (10967260839 / 1000000000000), orderedInterval (24670734601 / 1000000000000) (24670734602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2332482722870973 / 4000000000000) 3 (IntervalRat.scale (939 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13785151520 / 1000000000000) (-13785151412 / 1000000000000), orderedInterval (30040407053 / 1000000000000) (30040407161 / 1000000000000)))) (orderedInterval (23721938512 / 1000000000000) (23721938971 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate598_chunkChecks3 :
    compactCertificate598.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate598.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate598_chunkChecks3_0
    compactCertificate598_chunkChecks3_1 compactCertificate598_chunkChecks3_2

theorem compactCertificate598_chunkChecks4_0 :
    compactCertificate598.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (939 / 2) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30033089895 / 1000000000000) (-30033027386 / 1000000000000), orderedInterval (21338470775 / 1000000000000) (21338533284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1383326300079039 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37032220639 / 1000000000000) (37032220640 / 1000000000000), orderedInterval (21613284350 / 1000000000000) (21613284351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (447339303213087 / 800000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (23142705449 / 1000000000000) (23142705450 / 1000000000000), orderedInterval (24533639158 / 1000000000000) (24533639159 / 1000000000000)))) (orderedInterval (-9023127225 / 1000000000000) (-9023102285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (403651164298173 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73006820249 / 1000000000000) (73006820250 / 1000000000000), orderedInterval (30920285149 / 1000000000000) (30920285150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2943987151383477 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29319812704 / 1000000000000) (29319817794 / 1000000000000), orderedInterval (-2327414092 / 1000000000000) (-2327409003 / 1000000000000)))) (orderedInterval (-12390712468 / 1000000000000) (-12390710070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2168527611076701 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18735427219 / 1000000000000) (18735428182 / 1000000000000), orderedInterval (-28710021038 / 1000000000000) (-28710020074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3715809022949073 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4529673583 / 1000000000000) (-4529673582 / 1000000000000), orderedInterval (25785991231 / 1000000000000) (25785991232 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2737048108366707 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5462089146 / 1000000000000) (5462089147 / 1000000000000), orderedInterval (30005008554 / 1000000000000) (30005008555 / 1000000000000)))) (orderedInterval (2720154983 / 1000000000000) (2720155258 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate598_chunkChecks4_1 :
    compactCertificate598.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4199335661744061 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23898470702 / 1000000000000) (23898471515 / 1000000000000), orderedInterval (5926923768 / 1000000000000) (5926924580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2424487574725269 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17752638368 / 1000000000000) (-17752638367 / 1000000000000), orderedInterval (-27099196781 / 1000000000000) (-27099196780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4302295747042521 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22737017712 / 1000000000000) (22737056544 / 1000000000000), orderedInterval (-8665963531 / 1000000000000) (-8665924699 / 1000000000000)))) (orderedInterval (-20920953177 / 1000000000000) (-20920793209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4019762766013149 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10178282881 / 1000000000000) (10178282882 / 1000000000000), orderedInterval (23014329976 / 1000000000000) (23014329977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2868692385041517 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29631725800 / 1000000000000) (29631731834 / 1000000000000), orderedInterval (-3125466929 / 1000000000000) (-3125460895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3252791416613643 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8551447895 / 1000000000000) (-8551447894 / 1000000000000), orderedInterval (-26635547081 / 1000000000000) (-26635547080 / 1000000000000)))) (orderedInterval (11769241079 / 1000000000000) (11769244637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2711838362619867 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4906000359 / 1000000000000) (4906000360 / 1000000000000), orderedInterval (30244598023 / 1000000000000) (30244598024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2395991435181207 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8417193981 / 1000000000000) (8417193988 / 1000000000000), orderedInterval (-31502410802 / 1000000000000) (-31502410795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (694451706167493 / 800000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26543712973 / 1000000000000) (26543744955 / 1000000000000), orderedInterval (-5382671863 / 1000000000000) (-5382639881 / 1000000000000)))) (orderedInterval (6928878813 / 1000000000000) (6928888641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate598_chunkChecks4_2 :
    compactCertificate598.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1920889966250271 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12277817994 / 1000000000000) (-12277817993 / 1000000000000), orderedInterval (-34264504213 / 1000000000000) (-34264504212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1628359697664231 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20060664475 / 1000000000000) (-20060663225 / 1000000000000), orderedInterval (34103974731 / 1000000000000) (34103975980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1018951891633293 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43459523971 / 1000000000000) (-43459523970 / 1000000000000), orderedInterval (-24620636998 / 1000000000000) (-24620636997 / 1000000000000)))) (orderedInterval (2686896796 / 1000000000000) (2686896936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (547995716201331 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29445635273 / 1000000000000) (-29445633034 / 1000000000000), orderedInterval (61588111432 / 1000000000000) (61588113671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1487914969836993 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36597133573 / 1000000000000) (36597177072 / 1000000000000), orderedInterval (-19338811104 / 1000000000000) (-19338767605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2031620685548961 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-8679629658 / 1000000000000) (-8679629646 / 1000000000000), orderedInterval (34331817513 / 1000000000000) (34331817525 / 1000000000000)))) (orderedInterval (574445183 / 1000000000000) (574445630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (859048108366707 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51186407326 / 1000000000000) (51186412703 / 1000000000000), orderedInterval (-18673106629 / 1000000000000) (-18673101252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3491982867585747 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10967260838 / 1000000000000) (10967260839 / 1000000000000), orderedInterval (24670734601 / 1000000000000) (24670734602 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2332482722870973 / 4000000000000) 4 (IntervalRat.scale (939 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13785151520 / 1000000000000) (-13785151412 / 1000000000000), orderedInterval (30040407053 / 1000000000000) (30040407161 / 1000000000000)))) (orderedInterval (-4604795626 / 1000000000000) (-4604794908 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate598_chunkChecks4 :
    compactCertificate598.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate598.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate598_chunkChecks4_0
    compactCertificate598_chunkChecks4_1 compactCertificate598_chunkChecks4_2

theorem compactCertificate598_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate598.chunkCheck r b = true :=
  compactCertificate598.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate598_chunkChecks0
    · exact compactCertificate598_chunkChecks1
    · exact compactCertificate598_chunkChecks2
    · exact compactCertificate598_chunkChecks3
    · exact compactCertificate598_chunkChecks4)

theorem compactCertificate598_coefficient0 :
    compactCertificate598.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate598_coefficient1 :
    compactCertificate598.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate598_coefficient2 :
    compactCertificate598.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate598_coefficient3 :
    compactCertificate598.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate598_coefficient4 :
    compactCertificate598.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate598_coefficients : ∀ r : Fin 5,
    compactCertificate598.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate598_coefficient0
  · exact compactCertificate598_coefficient1
  · exact compactCertificate598_coefficient2
  · exact compactCertificate598_coefficient3
  · exact compactCertificate598_coefficient4

theorem compactCertificate598_lower : (1 : ℚ) ≤ compactCertificate598.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate598, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate598_proves {t : ℝ} (ht : t ∈ compactCertificate598.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate598.proves compactCertificate598_states compactCertificate598_chunks
    compactCertificate598_coefficients compactCertificate598_lower ht

end Erdos232
