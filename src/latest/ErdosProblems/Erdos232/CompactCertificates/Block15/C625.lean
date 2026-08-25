/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate625 : CompactCertificate where
  left := 496
  right := 497
  center := 993 / 2
  grid := fun i =>
    match i.val with
    | 0 => 158
    | 1 => 116
    | 2 => 188
    | 3 => 34
    | 4 => 91
    | 5 => 248
    | 6 => 183
    | 7 => 313
    | 8 => 230
    | 9 => 354
    | 10 => 204
    | 11 => 362
    | 12 => 338
    | 13 => 242
    | 14 => 274
    | 15 => 228
    | 16 => 202
    | 17 => 292
    | 18 => 162
    | 19 => 137
    | 20 => 86
    | 21 => 46
    | 22 => 125
    | 23 => 171
    | 24 => 72
    | 25 => 294
    | _ => 196
  point := fun i =>
    match i.val with
    | 0 => 993 / 2
    | 1 => 1462878611265693 / 4000000000000
    | 2 => 473064886145469 / 800000000000
    | 3 => 426864330296151 / 4000000000000
    | 4 => 1146617634610347 / 4000000000000
    | 5 => 3113289926862399 / 4000000000000
    | 6 => 2293235269221687 / 4000000000000
    | 7 => 3929497720754451 / 4000000000000
    | 8 => 2894450236004409 / 4000000000000
    | 9 => 4440831003314007 / 4000000000000
    | 10 => 2563914975188703 / 4000000000000
    | 11 => 4549712115882027 / 4000000000000
    | 12 => 4250931231790263 / 4000000000000
    | 13 => 3033665110059879 / 4000000000000
    | 14 => 3439852903831041 / 4000000000000
    | 15 => 2867790728521329 / 4000000000000
    | 16 => 2533780080015909 / 4000000000000
    | 17 => 734388226010991 / 800000000000
    | 18 => 2031356481881277 / 4000000000000
    | 19 => 1722003386347797 / 4000000000000
    | 20 => 1077549763995591 / 4000000000000
    | 21 => 579509846845497 / 4000000000000
    | 22 => 1573481964907491 / 4000000000000
    | 23 => 2148455101970307 / 4000000000000
    | 24 => 908450236004409 / 4000000000000
    | 25 => 3692799773708889 / 4000000000000
    | _ => 2466619109489751 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (28347469187 / 1000000000000) (28347469188 / 1000000000000), orderedInterval (21849201149 / 1000000000000) (21849201150 / 1000000000000))
    | 1 => (orderedInterval (36429662309 / 1000000000000) (36429714649 / 1000000000000), orderedInterval (-20387198611 / 1000000000000) (-20387146271 / 1000000000000))
    | 2 => (orderedInterval (32721784756 / 1000000000000) (32721785127 / 1000000000000), orderedInterval (2395566824 / 1000000000000) (2395567196 / 1000000000000))
    | 3 => (orderedInterval (48934771665 / 1000000000000) (48934771666 / 1000000000000), orderedInterval (59528136696 / 1000000000000) (59528136697 / 1000000000000))
    | 4 => (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))
    | 5 => (orderedInterval (-207597453 / 1000000000000) (-207597452 / 1000000000000), orderedInterval (28599003588 / 1000000000000) (28599003589 / 1000000000000))
    | 6 => (orderedInterval (24306191313 / 1000000000000) (24306202188 / 1000000000000), orderedInterval (-22816807722 / 1000000000000) (-22816796847 / 1000000000000))
    | 7 => (orderedInterval (4025536026 / 1000000000000) (4025536027 / 1000000000000), orderedInterval (-25138417338 / 1000000000000) (-25138417337 / 1000000000000))
    | 8 => (orderedInterval (28658981112 / 1000000000000) (28659009744 / 1000000000000), orderedInterval (-7664531382 / 1000000000000) (-7664502750 / 1000000000000))
    | 9 => (orderedInterval (-21665097146 / 1000000000000) (-21665080909 / 1000000000000), orderedInterval (10210135090 / 1000000000000) (10210151327 / 1000000000000))
    | 10 => (orderedInterval (24270709444 / 1000000000000) (24270709445 / 1000000000000), orderedInterval (20084104901 / 1000000000000) (20084104902 / 1000000000000))
    | 11 => (orderedInterval (19336600072 / 1000000000000) (19336600080 / 1000000000000), orderedInterval (13622238143 / 1000000000000) (13622238151 / 1000000000000))
    | 12 => (orderedInterval (24378466998 / 1000000000000) (24378495696 / 1000000000000), orderedInterval (-2186307768 / 1000000000000) (-2186279070 / 1000000000000))
    | 13 => (orderedInterval (-25329559843 / 1000000000000) (-25329514373 / 1000000000000), orderedInterval (14081568883 / 1000000000000) (14081614353 / 1000000000000))
    | 14 => (orderedInterval (-1303001326 / 1000000000000) (-1303001325 / 1000000000000), orderedInterval (27177761039 / 1000000000000) (27177761040 / 1000000000000))
    | 15 => (orderedInterval (29580698044 / 1000000000000) (29580698503 / 1000000000000), orderedInterval (3576668783 / 1000000000000) (3576669242 / 1000000000000))
    | 16 => (orderedInterval (-11508082470 / 1000000000000) (-11508082439 / 1000000000000), orderedInterval (29548483696 / 1000000000000) (29548483728 / 1000000000000))
    | 17 => (orderedInterval (26056800129 / 1000000000000) (26056801310 / 1000000000000), orderedInterval (3798908923 / 1000000000000) (3798910104 / 1000000000000))
    | 18 => (orderedInterval (-10926849206 / 1000000000000) (-10926849171 / 1000000000000), orderedInterval (33688495419 / 1000000000000) (33688495454 / 1000000000000))
    | 19 => (orderedInterval (-29828029192 / 1000000000000) (-29828029191 / 1000000000000), orderedInterval (-24236267981 / 1000000000000) (-24236267980 / 1000000000000))
    | 20 => (orderedInterval (-223280859 / 1000000000000) (-223280857 / 1000000000000), orderedInterval (48612827779 / 1000000000000) (48612827781 / 1000000000000))
    | 21 => (orderedInterval (60471473867 / 1000000000000) (60471473868 / 1000000000000), orderedInterval (26946011475 / 1000000000000) (26946011476 / 1000000000000))
    | 22 => (orderedInterval (-39966448847 / 1000000000000) (-39966448794 / 1000000000000), orderedInterval (-4537626190 / 1000000000000) (-4537626136 / 1000000000000))
    | 23 => (orderedInterval (-21823971960 / 1000000000000) (-21823971959 / 1000000000000), orderedInterval (-26606266728 / 1000000000000) (-26606266727 / 1000000000000))
    | 24 => (orderedInterval (52484110253 / 1000000000000) (52484110741 / 1000000000000), orderedInterval (-7080748558 / 1000000000000) (-7080748070 / 1000000000000))
    | 25 => (orderedInterval (9176059805 / 1000000000000) (9176059806 / 1000000000000), orderedInterval (24599491708 / 1000000000000) (24599491709 / 1000000000000))
    | _ => (orderedInterval (31910876950 / 1000000000000) (31910880980 / 1000000000000), orderedInterval (-3777110863 / 1000000000000) (-3777106833 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13495549820 / 1000000000000) (13495550365 / 1000000000000)
      | 1 => orderedInterval (-2236571310 / 1000000000000) (-2236571246 / 1000000000000)
      | 2 => orderedInterval (568467378 / 1000000000000) (568468098 / 1000000000000)
      | 3 => orderedInterval (8396694673 / 1000000000000) (8396697756 / 1000000000000)
      | 4 => orderedInterval (-2828748945 / 1000000000000) (-2828744068 / 1000000000000)
      | 5 => orderedInterval (1667314440 / 1000000000000) (1667314525 / 1000000000000)
      | 6 => orderedInterval (3428116706 / 1000000000000) (3428116836 / 1000000000000)
      | 7 => orderedInterval (1462664988 / 1000000000000) (1462665049 / 1000000000000)
      | _ => orderedInterval (-6417883983 / 1000000000000) (-6417883087 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (8687752260 / 1000000000000) (8687752685 / 1000000000000)
      | 1 => orderedInterval (-3340444127 / 1000000000000) (-3340444057 / 1000000000000)
      | 2 => orderedInterval (1264176232 / 1000000000000) (1264177290 / 1000000000000)
      | 3 => orderedInterval (2300635656 / 1000000000000) (2300642517 / 1000000000000)
      | 4 => orderedInterval (1880306366 / 1000000000000) (1880314139 / 1000000000000)
      | 5 => orderedInterval (-1917885050 / 1000000000000) (-1917884915 / 1000000000000)
      | 6 => orderedInterval (-3461452513 / 1000000000000) (-3461452392 / 1000000000000)
      | 7 => orderedInterval (2142245224 / 1000000000000) (2142245279 / 1000000000000)
      | _ => orderedInterval (-2862708474 / 1000000000000) (-2862707341 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14161316148 / 1000000000000) (-14161315806 / 1000000000000)
      | 1 => orderedInterval (568461826 / 1000000000000) (568461921 / 1000000000000)
      | 2 => orderedInterval (-987678410 / 1000000000000) (-987676851 / 1000000000000)
      | 3 => orderedInterval (-36676143778 / 1000000000000) (-36676128459 / 1000000000000)
      | 4 => orderedInterval (7581661810 / 1000000000000) (7581674391 / 1000000000000)
      | 5 => orderedInterval (-4061026304 / 1000000000000) (-4061026083 / 1000000000000)
      | 6 => orderedInterval (-3087980945 / 1000000000000) (-3087980829 / 1000000000000)
      | 7 => orderedInterval (-2435788914 / 1000000000000) (-2435788860 / 1000000000000)
      | _ => orderedInterval (11757969170 / 1000000000000) (11757970625 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8793266513 / 1000000000000) (-8793266229 / 1000000000000)
      | 1 => orderedInterval (7842192468 / 1000000000000) (7842192610 / 1000000000000)
      | 2 => orderedInterval (-5430523087 / 1000000000000) (-5430520785 / 1000000000000)
      | 3 => orderedInterval (-6126740557 / 1000000000000) (-6126706343 / 1000000000000)
      | 4 => orderedInterval (-4433783276 / 1000000000000) (-4433762576 / 1000000000000)
      | 5 => orderedInterval (2780619905 / 1000000000000) (2780620274 / 1000000000000)
      | 6 => orderedInterval (4623282978 / 1000000000000) (4623283091 / 1000000000000)
      | 7 => orderedInterval (-2615433075 / 1000000000000) (-2615433019 / 1000000000000)
      | _ => orderedInterval (11495923927 / 1000000000000) (11495925818 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15234742579 / 1000000000000) (15234742828 / 1000000000000)
      | 1 => orderedInterval (-134755761 / 1000000000000) (-134755544 / 1000000000000)
      | 2 => orderedInterval (1243923693 / 1000000000000) (1243927114 / 1000000000000)
      | 3 => orderedInterval (176972094945 / 1000000000000) (176972171487 / 1000000000000)
      | 4 => orderedInterval (-22201486498 / 1000000000000) (-22201451664 / 1000000000000)
      | 5 => orderedInterval (11015205529 / 1000000000000) (11015206161 / 1000000000000)
      | 6 => orderedInterval (2847254140 / 1000000000000) (2847254251 / 1000000000000)
      | 7 => orderedInterval (2650418139 / 1000000000000) (2650418197 / 1000000000000)
      | _ => orderedInterval (-23208304859 / 1000000000000) (-23208302347 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17535603767 / 1000000000000) (17535614228 / 1000000000000)
    | 1 => orderedInterval (4692625574 / 1000000000000) (4692643205 / 1000000000000)
    | 2 => orderedInterval (-41501841693 / 1000000000000) (-41501809951 / 1000000000000)
    | 3 => orderedInterval (-657727230 / 1000000000000) (-657667159 / 1000000000000)
    | _ => orderedInterval (164419091907 / 1000000000000) (164419210483 / 1000000000000)

theorem compactCertificate625_stateChecks0 :
    compactCertificate625.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (993 / 2)) (orderedInterval (28347469187 / 1000000000000) (28347469188 / 1000000000000), orderedInterval (21849201149 / 1000000000000) (21849201150 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1462878611265693 / 4000000000000)) (orderedInterval (36429662309 / 1000000000000) (36429714649 / 1000000000000), orderedInterval (-20387198611 / 1000000000000) (-20387146271 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (473064886145469 / 800000000000)) (orderedInterval (32721784756 / 1000000000000) (32721785127 / 1000000000000), orderedInterval (2395566824 / 1000000000000) (2395567196 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks1 :
    compactCertificate625.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (426864330296151 / 4000000000000)) (orderedInterval (48934771665 / 1000000000000) (48934771666 / 1000000000000), orderedInterval (59528136696 / 1000000000000) (59528136697 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1146617634610347 / 4000000000000)) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3113289926862399 / 4000000000000)) (orderedInterval (-207597453 / 1000000000000) (-207597452 / 1000000000000), orderedInterval (28599003588 / 1000000000000) (28599003589 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks2 :
    compactCertificate625.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2293235269221687 / 4000000000000)) (orderedInterval (24306191313 / 1000000000000) (24306202188 / 1000000000000), orderedInterval (-22816807722 / 1000000000000) (-22816796847 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 313 12 (3929497720754451 / 4000000000000)) (orderedInterval (4025536026 / 1000000000000) (4025536027 / 1000000000000), orderedInterval (-25138417338 / 1000000000000) (-25138417337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2894450236004409 / 4000000000000)) (orderedInterval (28658981112 / 1000000000000) (28659009744 / 1000000000000), orderedInterval (-7664531382 / 1000000000000) (-7664502750 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks3 :
    compactCertificate625.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 354 12 (4440831003314007 / 4000000000000)) (orderedInterval (-21665097146 / 1000000000000) (-21665080909 / 1000000000000), orderedInterval (10210135090 / 1000000000000) (10210151327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2563914975188703 / 4000000000000)) (orderedInterval (24270709444 / 1000000000000) (24270709445 / 1000000000000), orderedInterval (20084104901 / 1000000000000) (20084104902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 362 12 (4549712115882027 / 4000000000000)) (orderedInterval (19336600072 / 1000000000000) (19336600080 / 1000000000000), orderedInterval (13622238143 / 1000000000000) (13622238151 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks4 :
    compactCertificate625.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 338 12 (4250931231790263 / 4000000000000)) (orderedInterval (24378466998 / 1000000000000) (24378495696 / 1000000000000), orderedInterval (-2186307768 / 1000000000000) (-2186279070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3033665110059879 / 4000000000000)) (orderedInterval (-25329559843 / 1000000000000) (-25329514373 / 1000000000000), orderedInterval (14081568883 / 1000000000000) (14081614353 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (3439852903831041 / 4000000000000)) (orderedInterval (-1303001326 / 1000000000000) (-1303001325 / 1000000000000), orderedInterval (27177761039 / 1000000000000) (27177761040 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks5 :
    compactCertificate625.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2867790728521329 / 4000000000000)) (orderedInterval (29580698044 / 1000000000000) (29580698503 / 1000000000000), orderedInterval (3576668783 / 1000000000000) (3576669242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2533780080015909 / 4000000000000)) (orderedInterval (-11508082470 / 1000000000000) (-11508082439 / 1000000000000), orderedInterval (29548483696 / 1000000000000) (29548483728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (734388226010991 / 800000000000)) (orderedInterval (26056800129 / 1000000000000) (26056801310 / 1000000000000), orderedInterval (3798908923 / 1000000000000) (3798910104 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks6 :
    compactCertificate625.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2031356481881277 / 4000000000000)) (orderedInterval (-10926849206 / 1000000000000) (-10926849171 / 1000000000000), orderedInterval (33688495419 / 1000000000000) (33688495454 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1722003386347797 / 4000000000000)) (orderedInterval (-29828029192 / 1000000000000) (-29828029191 / 1000000000000), orderedInterval (-24236267981 / 1000000000000) (-24236267980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1077549763995591 / 4000000000000)) (orderedInterval (-223280859 / 1000000000000) (-223280857 / 1000000000000), orderedInterval (48612827779 / 1000000000000) (48612827781 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks7 :
    compactCertificate625.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (579509846845497 / 4000000000000)) (orderedInterval (60471473867 / 1000000000000) (60471473868 / 1000000000000), orderedInterval (26946011475 / 1000000000000) (26946011476 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1573481964907491 / 4000000000000)) (orderedInterval (-39966448847 / 1000000000000) (-39966448794 / 1000000000000), orderedInterval (-4537626190 / 1000000000000) (-4537626136 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2148455101970307 / 4000000000000)) (orderedInterval (-21823971960 / 1000000000000) (-21823971959 / 1000000000000), orderedInterval (-26606266728 / 1000000000000) (-26606266727 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_stateChecks8 :
    compactCertificate625.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (908450236004409 / 4000000000000)) (orderedInterval (52484110253 / 1000000000000) (52484110741 / 1000000000000), orderedInterval (-7080748558 / 1000000000000) (-7080748070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (3692799773708889 / 4000000000000)) (orderedInterval (9176059805 / 1000000000000) (9176059806 / 1000000000000), orderedInterval (24599491708 / 1000000000000) (24599491709 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2466619109489751 / 4000000000000)) (orderedInterval (31910876950 / 1000000000000) (31910880980 / 1000000000000), orderedInterval (-3777110863 / 1000000000000) (-3777106833 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_states : ∀ j,
    BesselStateValid (compactCertificate625.point j) (compactCertificate625.state j) :=
  compactCertificate625.statesValid_of_checks3 compactCertificate625_stateChecks0
    compactCertificate625_stateChecks1 compactCertificate625_stateChecks2
    compactCertificate625_stateChecks3 compactCertificate625_stateChecks4
    compactCertificate625_stateChecks5 compactCertificate625_stateChecks6
    compactCertificate625_stateChecks7 compactCertificate625_stateChecks8

theorem compactCertificate625_chunkChecks0_0 :
    compactCertificate625.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (993 / 2) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28347469187 / 1000000000000) (28347469188 / 1000000000000), orderedInterval (21849201149 / 1000000000000) (21849201150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1462878611265693 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36429662309 / 1000000000000) (36429714649 / 1000000000000), orderedInterval (-20387198611 / 1000000000000) (-20387146271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (473064886145469 / 800000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32721784756 / 1000000000000) (32721785127 / 1000000000000), orderedInterval (2395566824 / 1000000000000) (2395567196 / 1000000000000)))) (orderedInterval (13495549820 / 1000000000000) (13495550365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (426864330296151 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48934771665 / 1000000000000) (48934771666 / 1000000000000), orderedInterval (59528136696 / 1000000000000) (59528136697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3113289926862399 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-207597453 / 1000000000000) (-207597452 / 1000000000000), orderedInterval (28599003588 / 1000000000000) (28599003589 / 1000000000000)))) (orderedInterval (-2236571310 / 1000000000000) (-2236571246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2293235269221687 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24306191313 / 1000000000000) (24306202188 / 1000000000000), orderedInterval (-22816807722 / 1000000000000) (-22816796847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3929497720754451 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4025536026 / 1000000000000) (4025536027 / 1000000000000), orderedInterval (-25138417338 / 1000000000000) (-25138417337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2894450236004409 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28658981112 / 1000000000000) (28659009744 / 1000000000000), orderedInterval (-7664531382 / 1000000000000) (-7664502750 / 1000000000000)))) (orderedInterval (568467378 / 1000000000000) (568468098 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks0_1 :
    compactCertificate625.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4440831003314007 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21665097146 / 1000000000000) (-21665080909 / 1000000000000), orderedInterval (10210135090 / 1000000000000) (10210151327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2563914975188703 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24270709444 / 1000000000000) (24270709445 / 1000000000000), orderedInterval (20084104901 / 1000000000000) (20084104902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4549712115882027 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19336600072 / 1000000000000) (19336600080 / 1000000000000), orderedInterval (13622238143 / 1000000000000) (13622238151 / 1000000000000)))) (orderedInterval (8396694673 / 1000000000000) (8396697756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4250931231790263 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24378466998 / 1000000000000) (24378495696 / 1000000000000), orderedInterval (-2186307768 / 1000000000000) (-2186279070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3033665110059879 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25329559843 / 1000000000000) (-25329514373 / 1000000000000), orderedInterval (14081568883 / 1000000000000) (14081614353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3439852903831041 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1303001326 / 1000000000000) (-1303001325 / 1000000000000), orderedInterval (27177761039 / 1000000000000) (27177761040 / 1000000000000)))) (orderedInterval (-2828748945 / 1000000000000) (-2828744068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2867790728521329 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29580698044 / 1000000000000) (29580698503 / 1000000000000), orderedInterval (3576668783 / 1000000000000) (3576669242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2533780080015909 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11508082470 / 1000000000000) (-11508082439 / 1000000000000), orderedInterval (29548483696 / 1000000000000) (29548483728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (734388226010991 / 800000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26056800129 / 1000000000000) (26056801310 / 1000000000000), orderedInterval (3798908923 / 1000000000000) (3798910104 / 1000000000000)))) (orderedInterval (1667314440 / 1000000000000) (1667314525 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks0_2 :
    compactCertificate625.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2031356481881277 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10926849206 / 1000000000000) (-10926849171 / 1000000000000), orderedInterval (33688495419 / 1000000000000) (33688495454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1722003386347797 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29828029192 / 1000000000000) (-29828029191 / 1000000000000), orderedInterval (-24236267981 / 1000000000000) (-24236267980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1077549763995591 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-223280859 / 1000000000000) (-223280857 / 1000000000000), orderedInterval (48612827779 / 1000000000000) (48612827781 / 1000000000000)))) (orderedInterval (3428116706 / 1000000000000) (3428116836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (579509846845497 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60471473867 / 1000000000000) (60471473868 / 1000000000000), orderedInterval (26946011475 / 1000000000000) (26946011476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1573481964907491 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39966448847 / 1000000000000) (-39966448794 / 1000000000000), orderedInterval (-4537626190 / 1000000000000) (-4537626136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2148455101970307 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21823971960 / 1000000000000) (-21823971959 / 1000000000000), orderedInterval (-26606266728 / 1000000000000) (-26606266727 / 1000000000000)))) (orderedInterval (1462664988 / 1000000000000) (1462665049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (908450236004409 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52484110253 / 1000000000000) (52484110741 / 1000000000000), orderedInterval (-7080748558 / 1000000000000) (-7080748070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3692799773708889 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9176059805 / 1000000000000) (9176059806 / 1000000000000), orderedInterval (24599491708 / 1000000000000) (24599491709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2466619109489751 / 4000000000000) 0 (IntervalRat.scale (993 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31910876950 / 1000000000000) (31910880980 / 1000000000000), orderedInterval (-3777110863 / 1000000000000) (-3777106833 / 1000000000000)))) (orderedInterval (-6417883983 / 1000000000000) (-6417883087 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks0 :
    compactCertificate625.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate625.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate625_chunkChecks0_0
    compactCertificate625_chunkChecks0_1 compactCertificate625_chunkChecks0_2

theorem compactCertificate625_chunkChecks1_0 :
    compactCertificate625.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (993 / 2) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28347469187 / 1000000000000) (28347469188 / 1000000000000), orderedInterval (21849201149 / 1000000000000) (21849201150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1462878611265693 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36429662309 / 1000000000000) (36429714649 / 1000000000000), orderedInterval (-20387198611 / 1000000000000) (-20387146271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (473064886145469 / 800000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32721784756 / 1000000000000) (32721785127 / 1000000000000), orderedInterval (2395566824 / 1000000000000) (2395567196 / 1000000000000)))) (orderedInterval (8687752260 / 1000000000000) (8687752685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (426864330296151 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48934771665 / 1000000000000) (48934771666 / 1000000000000), orderedInterval (59528136696 / 1000000000000) (59528136697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3113289926862399 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-207597453 / 1000000000000) (-207597452 / 1000000000000), orderedInterval (28599003588 / 1000000000000) (28599003589 / 1000000000000)))) (orderedInterval (-3340444127 / 1000000000000) (-3340444057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2293235269221687 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24306191313 / 1000000000000) (24306202188 / 1000000000000), orderedInterval (-22816807722 / 1000000000000) (-22816796847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3929497720754451 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4025536026 / 1000000000000) (4025536027 / 1000000000000), orderedInterval (-25138417338 / 1000000000000) (-25138417337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2894450236004409 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28658981112 / 1000000000000) (28659009744 / 1000000000000), orderedInterval (-7664531382 / 1000000000000) (-7664502750 / 1000000000000)))) (orderedInterval (1264176232 / 1000000000000) (1264177290 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks1_1 :
    compactCertificate625.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4440831003314007 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21665097146 / 1000000000000) (-21665080909 / 1000000000000), orderedInterval (10210135090 / 1000000000000) (10210151327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2563914975188703 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24270709444 / 1000000000000) (24270709445 / 1000000000000), orderedInterval (20084104901 / 1000000000000) (20084104902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4549712115882027 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19336600072 / 1000000000000) (19336600080 / 1000000000000), orderedInterval (13622238143 / 1000000000000) (13622238151 / 1000000000000)))) (orderedInterval (2300635656 / 1000000000000) (2300642517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4250931231790263 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24378466998 / 1000000000000) (24378495696 / 1000000000000), orderedInterval (-2186307768 / 1000000000000) (-2186279070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3033665110059879 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25329559843 / 1000000000000) (-25329514373 / 1000000000000), orderedInterval (14081568883 / 1000000000000) (14081614353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3439852903831041 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1303001326 / 1000000000000) (-1303001325 / 1000000000000), orderedInterval (27177761039 / 1000000000000) (27177761040 / 1000000000000)))) (orderedInterval (1880306366 / 1000000000000) (1880314139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2867790728521329 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29580698044 / 1000000000000) (29580698503 / 1000000000000), orderedInterval (3576668783 / 1000000000000) (3576669242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2533780080015909 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11508082470 / 1000000000000) (-11508082439 / 1000000000000), orderedInterval (29548483696 / 1000000000000) (29548483728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (734388226010991 / 800000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26056800129 / 1000000000000) (26056801310 / 1000000000000), orderedInterval (3798908923 / 1000000000000) (3798910104 / 1000000000000)))) (orderedInterval (-1917885050 / 1000000000000) (-1917884915 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks1_2 :
    compactCertificate625.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2031356481881277 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10926849206 / 1000000000000) (-10926849171 / 1000000000000), orderedInterval (33688495419 / 1000000000000) (33688495454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1722003386347797 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29828029192 / 1000000000000) (-29828029191 / 1000000000000), orderedInterval (-24236267981 / 1000000000000) (-24236267980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1077549763995591 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-223280859 / 1000000000000) (-223280857 / 1000000000000), orderedInterval (48612827779 / 1000000000000) (48612827781 / 1000000000000)))) (orderedInterval (-3461452513 / 1000000000000) (-3461452392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (579509846845497 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60471473867 / 1000000000000) (60471473868 / 1000000000000), orderedInterval (26946011475 / 1000000000000) (26946011476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1573481964907491 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39966448847 / 1000000000000) (-39966448794 / 1000000000000), orderedInterval (-4537626190 / 1000000000000) (-4537626136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2148455101970307 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21823971960 / 1000000000000) (-21823971959 / 1000000000000), orderedInterval (-26606266728 / 1000000000000) (-26606266727 / 1000000000000)))) (orderedInterval (2142245224 / 1000000000000) (2142245279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (908450236004409 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52484110253 / 1000000000000) (52484110741 / 1000000000000), orderedInterval (-7080748558 / 1000000000000) (-7080748070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3692799773708889 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9176059805 / 1000000000000) (9176059806 / 1000000000000), orderedInterval (24599491708 / 1000000000000) (24599491709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2466619109489751 / 4000000000000) 1 (IntervalRat.scale (993 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31910876950 / 1000000000000) (31910880980 / 1000000000000), orderedInterval (-3777110863 / 1000000000000) (-3777106833 / 1000000000000)))) (orderedInterval (-2862708474 / 1000000000000) (-2862707341 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks1 :
    compactCertificate625.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate625.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate625_chunkChecks1_0
    compactCertificate625_chunkChecks1_1 compactCertificate625_chunkChecks1_2

theorem compactCertificate625_chunkChecks2_0 :
    compactCertificate625.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (993 / 2) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28347469187 / 1000000000000) (28347469188 / 1000000000000), orderedInterval (21849201149 / 1000000000000) (21849201150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1462878611265693 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36429662309 / 1000000000000) (36429714649 / 1000000000000), orderedInterval (-20387198611 / 1000000000000) (-20387146271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (473064886145469 / 800000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32721784756 / 1000000000000) (32721785127 / 1000000000000), orderedInterval (2395566824 / 1000000000000) (2395567196 / 1000000000000)))) (orderedInterval (-14161316148 / 1000000000000) (-14161315806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (426864330296151 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48934771665 / 1000000000000) (48934771666 / 1000000000000), orderedInterval (59528136696 / 1000000000000) (59528136697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3113289926862399 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-207597453 / 1000000000000) (-207597452 / 1000000000000), orderedInterval (28599003588 / 1000000000000) (28599003589 / 1000000000000)))) (orderedInterval (568461826 / 1000000000000) (568461921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2293235269221687 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24306191313 / 1000000000000) (24306202188 / 1000000000000), orderedInterval (-22816807722 / 1000000000000) (-22816796847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3929497720754451 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4025536026 / 1000000000000) (4025536027 / 1000000000000), orderedInterval (-25138417338 / 1000000000000) (-25138417337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2894450236004409 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28658981112 / 1000000000000) (28659009744 / 1000000000000), orderedInterval (-7664531382 / 1000000000000) (-7664502750 / 1000000000000)))) (orderedInterval (-987678410 / 1000000000000) (-987676851 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks2_1 :
    compactCertificate625.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4440831003314007 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21665097146 / 1000000000000) (-21665080909 / 1000000000000), orderedInterval (10210135090 / 1000000000000) (10210151327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2563914975188703 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24270709444 / 1000000000000) (24270709445 / 1000000000000), orderedInterval (20084104901 / 1000000000000) (20084104902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4549712115882027 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19336600072 / 1000000000000) (19336600080 / 1000000000000), orderedInterval (13622238143 / 1000000000000) (13622238151 / 1000000000000)))) (orderedInterval (-36676143778 / 1000000000000) (-36676128459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4250931231790263 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24378466998 / 1000000000000) (24378495696 / 1000000000000), orderedInterval (-2186307768 / 1000000000000) (-2186279070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3033665110059879 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25329559843 / 1000000000000) (-25329514373 / 1000000000000), orderedInterval (14081568883 / 1000000000000) (14081614353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3439852903831041 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1303001326 / 1000000000000) (-1303001325 / 1000000000000), orderedInterval (27177761039 / 1000000000000) (27177761040 / 1000000000000)))) (orderedInterval (7581661810 / 1000000000000) (7581674391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2867790728521329 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29580698044 / 1000000000000) (29580698503 / 1000000000000), orderedInterval (3576668783 / 1000000000000) (3576669242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2533780080015909 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11508082470 / 1000000000000) (-11508082439 / 1000000000000), orderedInterval (29548483696 / 1000000000000) (29548483728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (734388226010991 / 800000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26056800129 / 1000000000000) (26056801310 / 1000000000000), orderedInterval (3798908923 / 1000000000000) (3798910104 / 1000000000000)))) (orderedInterval (-4061026304 / 1000000000000) (-4061026083 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks2_2 :
    compactCertificate625.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2031356481881277 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10926849206 / 1000000000000) (-10926849171 / 1000000000000), orderedInterval (33688495419 / 1000000000000) (33688495454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1722003386347797 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29828029192 / 1000000000000) (-29828029191 / 1000000000000), orderedInterval (-24236267981 / 1000000000000) (-24236267980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1077549763995591 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-223280859 / 1000000000000) (-223280857 / 1000000000000), orderedInterval (48612827779 / 1000000000000) (48612827781 / 1000000000000)))) (orderedInterval (-3087980945 / 1000000000000) (-3087980829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (579509846845497 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60471473867 / 1000000000000) (60471473868 / 1000000000000), orderedInterval (26946011475 / 1000000000000) (26946011476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1573481964907491 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39966448847 / 1000000000000) (-39966448794 / 1000000000000), orderedInterval (-4537626190 / 1000000000000) (-4537626136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2148455101970307 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21823971960 / 1000000000000) (-21823971959 / 1000000000000), orderedInterval (-26606266728 / 1000000000000) (-26606266727 / 1000000000000)))) (orderedInterval (-2435788914 / 1000000000000) (-2435788860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (908450236004409 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52484110253 / 1000000000000) (52484110741 / 1000000000000), orderedInterval (-7080748558 / 1000000000000) (-7080748070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3692799773708889 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9176059805 / 1000000000000) (9176059806 / 1000000000000), orderedInterval (24599491708 / 1000000000000) (24599491709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2466619109489751 / 4000000000000) 2 (IntervalRat.scale (993 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31910876950 / 1000000000000) (31910880980 / 1000000000000), orderedInterval (-3777110863 / 1000000000000) (-3777106833 / 1000000000000)))) (orderedInterval (11757969170 / 1000000000000) (11757970625 / 1000000000000))) = true
  rfl'

theorem compactCertificate625_chunkChecks2 :
    compactCertificate625.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate625.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate625_chunkChecks2_0
    compactCertificate625_chunkChecks2_1 compactCertificate625_chunkChecks2_2

theorem compactCertificate625_chunkChecks3_0 :
    compactCertificate625.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (993 / 2) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28347469187 / 1000000000000) (28347469188 / 1000000000000), orderedInterval (21849201149 / 1000000000000) (21849201150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1462878611265693 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36429662309 / 1000000000000) (36429714649 / 1000000000000), orderedInterval (-20387198611 / 1000000000000) (-20387146271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (473064886145469 / 800000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32721784756 / 1000000000000) (32721785127 / 1000000000000), orderedInterval (2395566824 / 1000000000000) (2395567196 / 1000000000000)))) (orderedInterval (-8793266513 / 1000000000000) (-8793266229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (426864330296151 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48934771665 / 1000000000000) (48934771666 / 1000000000000), orderedInterval (59528136696 / 1000000000000) (59528136697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3113289926862399 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-207597453 / 1000000000000) (-207597452 / 1000000000000), orderedInterval (28599003588 / 1000000000000) (28599003589 / 1000000000000)))) (orderedInterval (7842192468 / 1000000000000) (7842192610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2293235269221687 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24306191313 / 1000000000000) (24306202188 / 1000000000000), orderedInterval (-22816807722 / 1000000000000) (-22816796847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3929497720754451 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4025536026 / 1000000000000) (4025536027 / 1000000000000), orderedInterval (-25138417338 / 1000000000000) (-25138417337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2894450236004409 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28658981112 / 1000000000000) (28659009744 / 1000000000000), orderedInterval (-7664531382 / 1000000000000) (-7664502750 / 1000000000000)))) (orderedInterval (-5430523087 / 1000000000000) (-5430520785 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate625_chunkChecks3_1 :
    compactCertificate625.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4440831003314007 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21665097146 / 1000000000000) (-21665080909 / 1000000000000), orderedInterval (10210135090 / 1000000000000) (10210151327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2563914975188703 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24270709444 / 1000000000000) (24270709445 / 1000000000000), orderedInterval (20084104901 / 1000000000000) (20084104902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4549712115882027 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19336600072 / 1000000000000) (19336600080 / 1000000000000), orderedInterval (13622238143 / 1000000000000) (13622238151 / 1000000000000)))) (orderedInterval (-6126740557 / 1000000000000) (-6126706343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4250931231790263 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24378466998 / 1000000000000) (24378495696 / 1000000000000), orderedInterval (-2186307768 / 1000000000000) (-2186279070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3033665110059879 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25329559843 / 1000000000000) (-25329514373 / 1000000000000), orderedInterval (14081568883 / 1000000000000) (14081614353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3439852903831041 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1303001326 / 1000000000000) (-1303001325 / 1000000000000), orderedInterval (27177761039 / 1000000000000) (27177761040 / 1000000000000)))) (orderedInterval (-4433783276 / 1000000000000) (-4433762576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2867790728521329 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29580698044 / 1000000000000) (29580698503 / 1000000000000), orderedInterval (3576668783 / 1000000000000) (3576669242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2533780080015909 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11508082470 / 1000000000000) (-11508082439 / 1000000000000), orderedInterval (29548483696 / 1000000000000) (29548483728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (734388226010991 / 800000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26056800129 / 1000000000000) (26056801310 / 1000000000000), orderedInterval (3798908923 / 1000000000000) (3798910104 / 1000000000000)))) (orderedInterval (2780619905 / 1000000000000) (2780620274 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate625_chunkChecks3_2 :
    compactCertificate625.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2031356481881277 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10926849206 / 1000000000000) (-10926849171 / 1000000000000), orderedInterval (33688495419 / 1000000000000) (33688495454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1722003386347797 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29828029192 / 1000000000000) (-29828029191 / 1000000000000), orderedInterval (-24236267981 / 1000000000000) (-24236267980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1077549763995591 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-223280859 / 1000000000000) (-223280857 / 1000000000000), orderedInterval (48612827779 / 1000000000000) (48612827781 / 1000000000000)))) (orderedInterval (4623282978 / 1000000000000) (4623283091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (579509846845497 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60471473867 / 1000000000000) (60471473868 / 1000000000000), orderedInterval (26946011475 / 1000000000000) (26946011476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1573481964907491 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39966448847 / 1000000000000) (-39966448794 / 1000000000000), orderedInterval (-4537626190 / 1000000000000) (-4537626136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2148455101970307 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21823971960 / 1000000000000) (-21823971959 / 1000000000000), orderedInterval (-26606266728 / 1000000000000) (-26606266727 / 1000000000000)))) (orderedInterval (-2615433075 / 1000000000000) (-2615433019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (908450236004409 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52484110253 / 1000000000000) (52484110741 / 1000000000000), orderedInterval (-7080748558 / 1000000000000) (-7080748070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3692799773708889 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9176059805 / 1000000000000) (9176059806 / 1000000000000), orderedInterval (24599491708 / 1000000000000) (24599491709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2466619109489751 / 4000000000000) 3 (IntervalRat.scale (993 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31910876950 / 1000000000000) (31910880980 / 1000000000000), orderedInterval (-3777110863 / 1000000000000) (-3777106833 / 1000000000000)))) (orderedInterval (11495923927 / 1000000000000) (11495925818 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate625_chunkChecks3 :
    compactCertificate625.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate625.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate625_chunkChecks3_0
    compactCertificate625_chunkChecks3_1 compactCertificate625_chunkChecks3_2

theorem compactCertificate625_chunkChecks4_0 :
    compactCertificate625.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (993 / 2) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (28347469187 / 1000000000000) (28347469188 / 1000000000000), orderedInterval (21849201149 / 1000000000000) (21849201150 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1462878611265693 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36429662309 / 1000000000000) (36429714649 / 1000000000000), orderedInterval (-20387198611 / 1000000000000) (-20387146271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (473064886145469 / 800000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32721784756 / 1000000000000) (32721785127 / 1000000000000), orderedInterval (2395566824 / 1000000000000) (2395567196 / 1000000000000)))) (orderedInterval (15234742579 / 1000000000000) (15234742828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (426864330296151 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48934771665 / 1000000000000) (48934771666 / 1000000000000), orderedInterval (59528136696 / 1000000000000) (59528136697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3113289926862399 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-207597453 / 1000000000000) (-207597452 / 1000000000000), orderedInterval (28599003588 / 1000000000000) (28599003589 / 1000000000000)))) (orderedInterval (-134755761 / 1000000000000) (-134755544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2293235269221687 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24306191313 / 1000000000000) (24306202188 / 1000000000000), orderedInterval (-22816807722 / 1000000000000) (-22816796847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3929497720754451 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4025536026 / 1000000000000) (4025536027 / 1000000000000), orderedInterval (-25138417338 / 1000000000000) (-25138417337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2894450236004409 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28658981112 / 1000000000000) (28659009744 / 1000000000000), orderedInterval (-7664531382 / 1000000000000) (-7664502750 / 1000000000000)))) (orderedInterval (1243923693 / 1000000000000) (1243927114 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate625_chunkChecks4_1 :
    compactCertificate625.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4440831003314007 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21665097146 / 1000000000000) (-21665080909 / 1000000000000), orderedInterval (10210135090 / 1000000000000) (10210151327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2563914975188703 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24270709444 / 1000000000000) (24270709445 / 1000000000000), orderedInterval (20084104901 / 1000000000000) (20084104902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4549712115882027 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19336600072 / 1000000000000) (19336600080 / 1000000000000), orderedInterval (13622238143 / 1000000000000) (13622238151 / 1000000000000)))) (orderedInterval (176972094945 / 1000000000000) (176972171487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4250931231790263 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24378466998 / 1000000000000) (24378495696 / 1000000000000), orderedInterval (-2186307768 / 1000000000000) (-2186279070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3033665110059879 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25329559843 / 1000000000000) (-25329514373 / 1000000000000), orderedInterval (14081568883 / 1000000000000) (14081614353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3439852903831041 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1303001326 / 1000000000000) (-1303001325 / 1000000000000), orderedInterval (27177761039 / 1000000000000) (27177761040 / 1000000000000)))) (orderedInterval (-22201486498 / 1000000000000) (-22201451664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2867790728521329 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29580698044 / 1000000000000) (29580698503 / 1000000000000), orderedInterval (3576668783 / 1000000000000) (3576669242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2533780080015909 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11508082470 / 1000000000000) (-11508082439 / 1000000000000), orderedInterval (29548483696 / 1000000000000) (29548483728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (734388226010991 / 800000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26056800129 / 1000000000000) (26056801310 / 1000000000000), orderedInterval (3798908923 / 1000000000000) (3798910104 / 1000000000000)))) (orderedInterval (11015205529 / 1000000000000) (11015206161 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate625_chunkChecks4_2 :
    compactCertificate625.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2031356481881277 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10926849206 / 1000000000000) (-10926849171 / 1000000000000), orderedInterval (33688495419 / 1000000000000) (33688495454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1722003386347797 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-29828029192 / 1000000000000) (-29828029191 / 1000000000000), orderedInterval (-24236267981 / 1000000000000) (-24236267980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1077549763995591 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-223280859 / 1000000000000) (-223280857 / 1000000000000), orderedInterval (48612827779 / 1000000000000) (48612827781 / 1000000000000)))) (orderedInterval (2847254140 / 1000000000000) (2847254251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (579509846845497 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60471473867 / 1000000000000) (60471473868 / 1000000000000), orderedInterval (26946011475 / 1000000000000) (26946011476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1573481964907491 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39966448847 / 1000000000000) (-39966448794 / 1000000000000), orderedInterval (-4537626190 / 1000000000000) (-4537626136 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2148455101970307 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21823971960 / 1000000000000) (-21823971959 / 1000000000000), orderedInterval (-26606266728 / 1000000000000) (-26606266727 / 1000000000000)))) (orderedInterval (2650418139 / 1000000000000) (2650418197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (908450236004409 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (52484110253 / 1000000000000) (52484110741 / 1000000000000), orderedInterval (-7080748558 / 1000000000000) (-7080748070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3692799773708889 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9176059805 / 1000000000000) (9176059806 / 1000000000000), orderedInterval (24599491708 / 1000000000000) (24599491709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2466619109489751 / 4000000000000) 4 (IntervalRat.scale (993 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31910876950 / 1000000000000) (31910880980 / 1000000000000), orderedInterval (-3777110863 / 1000000000000) (-3777106833 / 1000000000000)))) (orderedInterval (-23208304859 / 1000000000000) (-23208302347 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate625_chunkChecks4 :
    compactCertificate625.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate625.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate625_chunkChecks4_0
    compactCertificate625_chunkChecks4_1 compactCertificate625_chunkChecks4_2

theorem compactCertificate625_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate625.chunkCheck r b = true :=
  compactCertificate625.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate625_chunkChecks0
    · exact compactCertificate625_chunkChecks1
    · exact compactCertificate625_chunkChecks2
    · exact compactCertificate625_chunkChecks3
    · exact compactCertificate625_chunkChecks4)

theorem compactCertificate625_coefficient0 :
    compactCertificate625.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate625_coefficient1 :
    compactCertificate625.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate625_coefficient2 :
    compactCertificate625.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate625_coefficient3 :
    compactCertificate625.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate625_coefficient4 :
    compactCertificate625.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate625_coefficients : ∀ r : Fin 5,
    compactCertificate625.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate625_coefficient0
  · exact compactCertificate625_coefficient1
  · exact compactCertificate625_coefficient2
  · exact compactCertificate625_coefficient3
  · exact compactCertificate625_coefficient4

theorem compactCertificate625_lower : (1 : ℚ) ≤ compactCertificate625.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate625, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate625_proves {t : ℝ} (ht : t ∈ compactCertificate625.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate625.proves compactCertificate625_states compactCertificate625_chunks
    compactCertificate625_coefficients compactCertificate625_lower ht

end Erdos232
