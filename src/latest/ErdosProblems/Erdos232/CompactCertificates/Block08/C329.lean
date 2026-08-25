/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate329 : CompactCertificate where
  left := 201
  right := 202
  center := 403 / 2
  grid := fun i =>
    match i.val with
    | 0 => 64
    | 1 => 47
    | 2 => 76
    | 3 => 14
    | 4 => 37
    | 5 => 101
    | 6 => 74
    | 7 => 127
    | 8 => 94
    | 9 => 143
    | 10 => 83
    | 11 => 147
    | 12 => 137
    | 13 => 98
    | 14 => 111
    | 15 => 93
    | 16 => 82
    | 17 => 119
    | 18 => 66
    | 19 => 56
    | 20 => 35
    | 21 => 19
    | 22 => 51
    | 23 => 69
    | 24 => 29
    | 25 => 119
    | _ => 80
  point := fun i =>
    match i.val with
    | 0 => 403 / 2
    | 1 => 593695952004103 / 4000000000000
    | 2 => 191989072624999 / 800000000000
    | 3 => 173238998096021 / 4000000000000
    | 4 => 465344316966737 / 4000000000000
    | 5 => 1263500342926029 / 4000000000000
    | 6 => 930688633933877 / 4000000000000
    | 7 => 1594750837325321 / 4000000000000
    | 8 => 1174686248851739 / 4000000000000
    | 9 => 1802270789864597 / 4000000000000
    | 10 => 1040541525680813 / 4000000000000
    | 11 => 1846459197080017 / 4000000000000
    | 12 => 1725201698299573 / 4000000000000
    | 13 => 1231185336711109 / 4000000000000
    | 14 => 1396032950900211 / 4000000000000
    | 15 => 1163866730709059 / 4000000000000
    | 16 => 1028311553118239 / 4000000000000
    | 17 => 298044768461661 / 800000000000
    | 18 => 824407514801767 / 4000000000000
    | 19 => 698859380360687 / 4000000000000
    | 20 => 437313751148261 / 4000000000000
    | 21 => 235188789807387 / 4000000000000
    | 22 => 638583315063161 / 4000000000000
    | 23 => 871930922551897 / 4000000000000
    | 24 => 368686248851739 / 4000000000000
    | 25 => 1498689132733819 / 4000000000000
    | _ => 1001054885321621 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (52840147774 / 1000000000000) (52840147775 / 1000000000000), orderedInterval (19034338551 / 1000000000000) (19034338552 / 1000000000000))
    | 1 => (orderedInterval (-65482195168 / 1000000000000) (-65482195131 / 1000000000000), orderedInterval (-899733218 / 1000000000000) (-899733182 / 1000000000000))
    | 2 => (orderedInterval (46612488402 / 1000000000000) (46612503741 / 1000000000000), orderedInterval (-22006135333 / 1000000000000) (-22006119994 / 1000000000000))
    | 3 => (orderedInterval (13304918440 / 1000000000000) (13304918442 / 1000000000000), orderedInterval (120358491679 / 1000000000000) (120358491681 / 1000000000000))
    | 4 => (orderedInterval (-57084315456 / 1000000000000) (-57084315455 / 1000000000000), orderedInterval (-46803768303 / 1000000000000) (-46803768302 / 1000000000000))
    | 5 => (orderedInterval (26837819018 / 1000000000000) (26837825836 / 1000000000000), orderedInterval (-36030652758 / 1000000000000) (-36030645941 / 1000000000000))
    | 6 => (orderedInterval (43417178833 / 1000000000000) (43417178834 / 1000000000000), orderedInterval (29079798925 / 1000000000000) (29079798926 / 1000000000000))
    | 7 => (orderedInterval (-18824700254 / 1000000000000) (-18824700253 / 1000000000000), orderedInterval (-35224362074 / 1000000000000) (-35224362073 / 1000000000000))
    | 8 => (orderedInterval (-35076684340 / 1000000000000) (-35076627812 / 1000000000000), orderedInterval (30677052727 / 1000000000000) (30677109254 / 1000000000000))
    | 9 => (orderedInterval (-32350553469 / 1000000000000) (-32350459568 / 1000000000000), orderedInterval (19176707050 / 1000000000000) (19176800951 / 1000000000000))
    | 10 => (orderedInterval (-8277190474 / 1000000000000) (-8277190473 / 1000000000000), orderedInterval (-48756579705 / 1000000000000) (-48756579704 / 1000000000000))
    | 11 => (orderedInterval (-20531675492 / 1000000000000) (-20531675491 / 1000000000000), orderedInterval (-30922313932 / 1000000000000) (-30922313931 / 1000000000000))
    | 12 => (orderedInterval (-38158731101 / 1000000000000) (-38158729691 / 1000000000000), orderedInterval (4511617928 / 1000000000000) (4511619337 / 1000000000000))
    | 13 => (orderedInterval (29480262931 / 1000000000000) (29480262932 / 1000000000000), orderedInterval (34582004403 / 1000000000000) (34582004404 / 1000000000000))
    | 14 => (orderedInterval (-37596937236 / 1000000000000) (-37596937235 / 1000000000000), orderedInterval (-20208211710 / 1000000000000) (-20208211709 / 1000000000000))
    | 15 => (orderedInterval (18922108254 / 1000000000000) (18922108886 / 1000000000000), orderedInterval (-42809885116 / 1000000000000) (-42809884484 / 1000000000000))
    | 16 => (orderedInterval (12417755706 / 1000000000000) (12417755707 / 1000000000000), orderedInterval (48164775235 / 1000000000000) (48164775236 / 1000000000000))
    | 17 => (orderedInterval (20125975680 / 1000000000000) (20125976844 / 1000000000000), orderedInterval (-36134289490 / 1000000000000) (-36134288326 / 1000000000000))
    | 18 => (orderedInterval (-24596013792 / 1000000000000) (-24596012064 / 1000000000000), orderedInterval (49898421332 / 1000000000000) (49898423060 / 1000000000000))
    | 19 => (orderedInterval (-25145159503 / 1000000000000) (-25145158015 / 1000000000000), orderedInterval (54949052411 / 1000000000000) (54949053900 / 1000000000000))
    | 20 => (orderedInterval (-11927445856 / 1000000000000) (-11927445855 / 1000000000000), orderedInterval (-75316511233 / 1000000000000) (-75316511231 / 1000000000000))
    | 21 => (orderedInterval (11401068631 / 1000000000000) (11401068679 / 1000000000000), orderedInterval (-103527020850 / 1000000000000) (-103527020802 / 1000000000000))
    | 22 => (orderedInterval (-13115582093 / 1000000000000) (-13115582092 / 1000000000000), orderedInterval (-61730275933 / 1000000000000) (-61730275932 / 1000000000000))
    | 23 => (orderedInterval (-49192361151 / 1000000000000) (-49192348964 / 1000000000000), orderedInterval (22487203865 / 1000000000000) (22487216052 / 1000000000000))
    | 24 => (orderedInterval (-79902175189 / 1000000000000) (-79902173918 / 1000000000000), orderedInterval (23290733628 / 1000000000000) (23290734899 / 1000000000000))
    | 25 => (orderedInterval (-41192327548 / 1000000000000) (-41192327171 / 1000000000000), orderedInterval (1580840971 / 1000000000000) (1580841348 / 1000000000000))
    | _ => (orderedInterval (-13879723572 / 1000000000000) (-13879723435 / 1000000000000), orderedInterval (48516422097 / 1000000000000) (48516422234 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (23069091729 / 1000000000000) (23069092645 / 1000000000000)
      | 1 => orderedInterval (-4136488375 / 1000000000000) (-4136487865 / 1000000000000)
      | 2 => orderedInterval (-267105187 / 1000000000000) (-267103809 / 1000000000000)
      | 3 => orderedInterval (2216315681 / 1000000000000) (2216332446 / 1000000000000)
      | 4 => orderedInterval (3666883128 / 1000000000000) (3666883178 / 1000000000000)
      | 5 => orderedInterval (23183832 / 1000000000000) (23183889 / 1000000000000)
      | 6 => orderedInterval (4967630012 / 1000000000000) (4967630424 / 1000000000000)
      | 7 => orderedInterval (3857075359 / 1000000000000) (3857076318 / 1000000000000)
      | _ => orderedInterval (5475656386 / 1000000000000) (5475656507 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6000379009 / 1000000000000) (6000380098 / 1000000000000)
      | 1 => orderedInterval (2748014551 / 1000000000000) (2748015338 / 1000000000000)
      | 2 => orderedInterval (3230211282 / 1000000000000) (3230213294 / 1000000000000)
      | 3 => orderedInterval (-22353317384 / 1000000000000) (-22353279908 / 1000000000000)
      | 4 => orderedInterval (4998064276 / 1000000000000) (4998064370 / 1000000000000)
      | 5 => orderedInterval (-5940985404 / 1000000000000) (-5940985310 / 1000000000000)
      | 6 => orderedInterval (-12187643433 / 1000000000000) (-12187643030 / 1000000000000)
      | 7 => orderedInterval (-196986243 / 1000000000000) (-196985210 / 1000000000000)
      | _ => orderedInterval (-11480969714 / 1000000000000) (-11480969543 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-24522633554 / 1000000000000) (-24522632253 / 1000000000000)
      | 1 => orderedInterval (5376282995 / 1000000000000) (5376284229 / 1000000000000)
      | 2 => orderedInterval (-488444879 / 1000000000000) (-488441931 / 1000000000000)
      | 3 => orderedInterval (-12290582158 / 1000000000000) (-12290498191 / 1000000000000)
      | 4 => orderedInterval (-10256444337 / 1000000000000) (-10256444154 / 1000000000000)
      | 5 => orderedInterval (-1030990669 / 1000000000000) (-1030990509 / 1000000000000)
      | 6 => orderedInterval (-5009595496 / 1000000000000) (-5009595097 / 1000000000000)
      | 7 => orderedInterval (-4579930107 / 1000000000000) (-4579928987 / 1000000000000)
      | _ => orderedInterval (-15452609694 / 1000000000000) (-15452609430 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-5237740054 / 1000000000000) (-5237738505 / 1000000000000)
      | 1 => orderedInterval (-9552096696 / 1000000000000) (-9552094765 / 1000000000000)
      | 2 => orderedInterval (-10708315008 / 1000000000000) (-10708310700 / 1000000000000)
      | 3 => orderedInterval (98780603586 / 1000000000000) (98780791322 / 1000000000000)
      | 4 => orderedInterval (-11337270912 / 1000000000000) (-11337270552 / 1000000000000)
      | 5 => orderedInterval (13064992920 / 1000000000000) (13064993195 / 1000000000000)
      | 6 => orderedInterval (10981198345 / 1000000000000) (10981198741 / 1000000000000)
      | 7 => orderedInterval (1460584356 / 1000000000000) (1460585567 / 1000000000000)
      | _ => orderedInterval (18330448468 / 1000000000000) (18330448895 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (26319341586 / 1000000000000) (26319343438 / 1000000000000)
      | 1 => orderedInterval (-11658606240 / 1000000000000) (-11658603206 / 1000000000000)
      | 2 => orderedInterval (5180257483 / 1000000000000) (5180263807 / 1000000000000)
      | 3 => orderedInterval (60631767837 / 1000000000000) (60632188541 / 1000000000000)
      | 4 => orderedInterval (31462200734 / 1000000000000) (31462201462 / 1000000000000)
      | 5 => orderedInterval (4959391199 / 1000000000000) (4959391683 / 1000000000000)
      | 6 => orderedInterval (4966140025 / 1000000000000) (4966140421 / 1000000000000)
      | 7 => orderedInterval (5264496775 / 1000000000000) (5264498089 / 1000000000000)
      | _ => orderedInterval (46076013986 / 1000000000000) (46076014704 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (38872242565 / 1000000000000) (38872263733 / 1000000000000)
    | 1 => orderedInterval (-35183233060 / 1000000000000) (-35183189901 / 1000000000000)
    | 2 => orderedInterval (-68254947899 / 1000000000000) (-68254856323 / 1000000000000)
    | 3 => orderedInterval (105782405005 / 1000000000000) (105782603198 / 1000000000000)
    | _ => orderedInterval (173201003385 / 1000000000000) (173201438939 / 1000000000000)

theorem compactCertificate329_stateChecks0 :
    compactCertificate329.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (403 / 2)) (orderedInterval (52840147774 / 1000000000000) (52840147775 / 1000000000000), orderedInterval (19034338551 / 1000000000000) (19034338552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (593695952004103 / 4000000000000)) (orderedInterval (-65482195168 / 1000000000000) (-65482195131 / 1000000000000), orderedInterval (-899733218 / 1000000000000) (-899733182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (191989072624999 / 800000000000)) (orderedInterval (46612488402 / 1000000000000) (46612503741 / 1000000000000), orderedInterval (-22006135333 / 1000000000000) (-22006119994 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks1 :
    compactCertificate329.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (173238998096021 / 4000000000000)) (orderedInterval (13304918440 / 1000000000000) (13304918442 / 1000000000000), orderedInterval (120358491679 / 1000000000000) (120358491681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (465344316966737 / 4000000000000)) (orderedInterval (-57084315456 / 1000000000000) (-57084315455 / 1000000000000), orderedInterval (-46803768303 / 1000000000000) (-46803768302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1263500342926029 / 4000000000000)) (orderedInterval (26837819018 / 1000000000000) (26837825836 / 1000000000000), orderedInterval (-36030652758 / 1000000000000) (-36030645941 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks2 :
    compactCertificate329.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (930688633933877 / 4000000000000)) (orderedInterval (43417178833 / 1000000000000) (43417178834 / 1000000000000), orderedInterval (29079798925 / 1000000000000) (29079798926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1594750837325321 / 4000000000000)) (orderedInterval (-18824700254 / 1000000000000) (-18824700253 / 1000000000000), orderedInterval (-35224362074 / 1000000000000) (-35224362073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1174686248851739 / 4000000000000)) (orderedInterval (-35076684340 / 1000000000000) (-35076627812 / 1000000000000), orderedInterval (30677052727 / 1000000000000) (30677109254 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks3 :
    compactCertificate329.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1802270789864597 / 4000000000000)) (orderedInterval (-32350553469 / 1000000000000) (-32350459568 / 1000000000000), orderedInterval (19176707050 / 1000000000000) (19176800951 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040541525680813 / 4000000000000)) (orderedInterval (-8277190474 / 1000000000000) (-8277190473 / 1000000000000), orderedInterval (-48756579705 / 1000000000000) (-48756579704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1846459197080017 / 4000000000000)) (orderedInterval (-20531675492 / 1000000000000) (-20531675491 / 1000000000000), orderedInterval (-30922313932 / 1000000000000) (-30922313931 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks4 :
    compactCertificate329.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1725201698299573 / 4000000000000)) (orderedInterval (-38158731101 / 1000000000000) (-38158729691 / 1000000000000), orderedInterval (4511617928 / 1000000000000) (4511619337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1231185336711109 / 4000000000000)) (orderedInterval (29480262931 / 1000000000000) (29480262932 / 1000000000000), orderedInterval (34582004403 / 1000000000000) (34582004404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1396032950900211 / 4000000000000)) (orderedInterval (-37596937236 / 1000000000000) (-37596937235 / 1000000000000), orderedInterval (-20208211710 / 1000000000000) (-20208211709 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks5 :
    compactCertificate329.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1163866730709059 / 4000000000000)) (orderedInterval (18922108254 / 1000000000000) (18922108886 / 1000000000000), orderedInterval (-42809885116 / 1000000000000) (-42809884484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1028311553118239 / 4000000000000)) (orderedInterval (12417755706 / 1000000000000) (12417755707 / 1000000000000), orderedInterval (48164775235 / 1000000000000) (48164775236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (298044768461661 / 800000000000)) (orderedInterval (20125975680 / 1000000000000) (20125976844 / 1000000000000), orderedInterval (-36134289490 / 1000000000000) (-36134288326 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks6 :
    compactCertificate329.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (824407514801767 / 4000000000000)) (orderedInterval (-24596013792 / 1000000000000) (-24596012064 / 1000000000000), orderedInterval (49898421332 / 1000000000000) (49898423060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (698859380360687 / 4000000000000)) (orderedInterval (-25145159503 / 1000000000000) (-25145158015 / 1000000000000), orderedInterval (54949052411 / 1000000000000) (54949053900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (437313751148261 / 4000000000000)) (orderedInterval (-11927445856 / 1000000000000) (-11927445855 / 1000000000000), orderedInterval (-75316511233 / 1000000000000) (-75316511231 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks7 :
    compactCertificate329.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (235188789807387 / 4000000000000)) (orderedInterval (11401068631 / 1000000000000) (11401068679 / 1000000000000), orderedInterval (-103527020850 / 1000000000000) (-103527020802 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (638583315063161 / 4000000000000)) (orderedInterval (-13115582093 / 1000000000000) (-13115582092 / 1000000000000), orderedInterval (-61730275933 / 1000000000000) (-61730275932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (871930922551897 / 4000000000000)) (orderedInterval (-49192361151 / 1000000000000) (-49192348964 / 1000000000000), orderedInterval (22487203865 / 1000000000000) (22487216052 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_stateChecks8 :
    compactCertificate329.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (368686248851739 / 4000000000000)) (orderedInterval (-79902175189 / 1000000000000) (-79902173918 / 1000000000000), orderedInterval (23290733628 / 1000000000000) (23290734899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1498689132733819 / 4000000000000)) (orderedInterval (-41192327548 / 1000000000000) (-41192327171 / 1000000000000), orderedInterval (1580840971 / 1000000000000) (1580841348 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1001054885321621 / 4000000000000)) (orderedInterval (-13879723572 / 1000000000000) (-13879723435 / 1000000000000), orderedInterval (48516422097 / 1000000000000) (48516422234 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_states : ∀ j,
    BesselStateValid (compactCertificate329.point j) (compactCertificate329.state j) :=
  compactCertificate329.statesValid_of_checks3 compactCertificate329_stateChecks0
    compactCertificate329_stateChecks1 compactCertificate329_stateChecks2
    compactCertificate329_stateChecks3 compactCertificate329_stateChecks4
    compactCertificate329_stateChecks5 compactCertificate329_stateChecks6
    compactCertificate329_stateChecks7 compactCertificate329_stateChecks8

theorem compactCertificate329_chunkChecks0_0 :
    compactCertificate329.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (403 / 2) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52840147774 / 1000000000000) (52840147775 / 1000000000000), orderedInterval (19034338551 / 1000000000000) (19034338552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (593695952004103 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65482195168 / 1000000000000) (-65482195131 / 1000000000000), orderedInterval (-899733218 / 1000000000000) (-899733182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (191989072624999 / 800000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46612488402 / 1000000000000) (46612503741 / 1000000000000), orderedInterval (-22006135333 / 1000000000000) (-22006119994 / 1000000000000)))) (orderedInterval (23069091729 / 1000000000000) (23069092645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (173238998096021 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13304918440 / 1000000000000) (13304918442 / 1000000000000), orderedInterval (120358491679 / 1000000000000) (120358491681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (465344316966737 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57084315456 / 1000000000000) (-57084315455 / 1000000000000), orderedInterval (-46803768303 / 1000000000000) (-46803768302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1263500342926029 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26837819018 / 1000000000000) (26837825836 / 1000000000000), orderedInterval (-36030652758 / 1000000000000) (-36030645941 / 1000000000000)))) (orderedInterval (-4136488375 / 1000000000000) (-4136487865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (930688633933877 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43417178833 / 1000000000000) (43417178834 / 1000000000000), orderedInterval (29079798925 / 1000000000000) (29079798926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1594750837325321 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18824700254 / 1000000000000) (-18824700253 / 1000000000000), orderedInterval (-35224362074 / 1000000000000) (-35224362073 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1174686248851739 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35076684340 / 1000000000000) (-35076627812 / 1000000000000), orderedInterval (30677052727 / 1000000000000) (30677109254 / 1000000000000)))) (orderedInterval (-267105187 / 1000000000000) (-267103809 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks0_1 :
    compactCertificate329.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1802270789864597 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32350553469 / 1000000000000) (-32350459568 / 1000000000000), orderedInterval (19176707050 / 1000000000000) (19176800951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1040541525680813 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8277190474 / 1000000000000) (-8277190473 / 1000000000000), orderedInterval (-48756579705 / 1000000000000) (-48756579704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1846459197080017 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20531675492 / 1000000000000) (-20531675491 / 1000000000000), orderedInterval (-30922313932 / 1000000000000) (-30922313931 / 1000000000000)))) (orderedInterval (2216315681 / 1000000000000) (2216332446 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1725201698299573 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38158731101 / 1000000000000) (-38158729691 / 1000000000000), orderedInterval (4511617928 / 1000000000000) (4511619337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1231185336711109 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29480262931 / 1000000000000) (29480262932 / 1000000000000), orderedInterval (34582004403 / 1000000000000) (34582004404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1396032950900211 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37596937236 / 1000000000000) (-37596937235 / 1000000000000), orderedInterval (-20208211710 / 1000000000000) (-20208211709 / 1000000000000)))) (orderedInterval (3666883128 / 1000000000000) (3666883178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1163866730709059 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18922108254 / 1000000000000) (18922108886 / 1000000000000), orderedInterval (-42809885116 / 1000000000000) (-42809884484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1028311553118239 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12417755706 / 1000000000000) (12417755707 / 1000000000000), orderedInterval (48164775235 / 1000000000000) (48164775236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (298044768461661 / 800000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20125975680 / 1000000000000) (20125976844 / 1000000000000), orderedInterval (-36134289490 / 1000000000000) (-36134288326 / 1000000000000)))) (orderedInterval (23183832 / 1000000000000) (23183889 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks0_2 :
    compactCertificate329.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (824407514801767 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24596013792 / 1000000000000) (-24596012064 / 1000000000000), orderedInterval (49898421332 / 1000000000000) (49898423060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (698859380360687 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25145159503 / 1000000000000) (-25145158015 / 1000000000000), orderedInterval (54949052411 / 1000000000000) (54949053900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (437313751148261 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11927445856 / 1000000000000) (-11927445855 / 1000000000000), orderedInterval (-75316511233 / 1000000000000) (-75316511231 / 1000000000000)))) (orderedInterval (4967630012 / 1000000000000) (4967630424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (235188789807387 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11401068631 / 1000000000000) (11401068679 / 1000000000000), orderedInterval (-103527020850 / 1000000000000) (-103527020802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (638583315063161 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13115582093 / 1000000000000) (-13115582092 / 1000000000000), orderedInterval (-61730275933 / 1000000000000) (-61730275932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (871930922551897 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-49192361151 / 1000000000000) (-49192348964 / 1000000000000), orderedInterval (22487203865 / 1000000000000) (22487216052 / 1000000000000)))) (orderedInterval (3857075359 / 1000000000000) (3857076318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (368686248851739 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79902175189 / 1000000000000) (-79902173918 / 1000000000000), orderedInterval (23290733628 / 1000000000000) (23290734899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1498689132733819 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41192327548 / 1000000000000) (-41192327171 / 1000000000000), orderedInterval (1580840971 / 1000000000000) (1580841348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1001054885321621 / 4000000000000) 0 (IntervalRat.scale (403 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13879723572 / 1000000000000) (-13879723435 / 1000000000000), orderedInterval (48516422097 / 1000000000000) (48516422234 / 1000000000000)))) (orderedInterval (5475656386 / 1000000000000) (5475656507 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks0 :
    compactCertificate329.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate329.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate329_chunkChecks0_0
    compactCertificate329_chunkChecks0_1 compactCertificate329_chunkChecks0_2

theorem compactCertificate329_chunkChecks1_0 :
    compactCertificate329.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (403 / 2) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52840147774 / 1000000000000) (52840147775 / 1000000000000), orderedInterval (19034338551 / 1000000000000) (19034338552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (593695952004103 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65482195168 / 1000000000000) (-65482195131 / 1000000000000), orderedInterval (-899733218 / 1000000000000) (-899733182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (191989072624999 / 800000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46612488402 / 1000000000000) (46612503741 / 1000000000000), orderedInterval (-22006135333 / 1000000000000) (-22006119994 / 1000000000000)))) (orderedInterval (6000379009 / 1000000000000) (6000380098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (173238998096021 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13304918440 / 1000000000000) (13304918442 / 1000000000000), orderedInterval (120358491679 / 1000000000000) (120358491681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (465344316966737 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57084315456 / 1000000000000) (-57084315455 / 1000000000000), orderedInterval (-46803768303 / 1000000000000) (-46803768302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1263500342926029 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26837819018 / 1000000000000) (26837825836 / 1000000000000), orderedInterval (-36030652758 / 1000000000000) (-36030645941 / 1000000000000)))) (orderedInterval (2748014551 / 1000000000000) (2748015338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (930688633933877 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43417178833 / 1000000000000) (43417178834 / 1000000000000), orderedInterval (29079798925 / 1000000000000) (29079798926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1594750837325321 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18824700254 / 1000000000000) (-18824700253 / 1000000000000), orderedInterval (-35224362074 / 1000000000000) (-35224362073 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1174686248851739 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35076684340 / 1000000000000) (-35076627812 / 1000000000000), orderedInterval (30677052727 / 1000000000000) (30677109254 / 1000000000000)))) (orderedInterval (3230211282 / 1000000000000) (3230213294 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks1_1 :
    compactCertificate329.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1802270789864597 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32350553469 / 1000000000000) (-32350459568 / 1000000000000), orderedInterval (19176707050 / 1000000000000) (19176800951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1040541525680813 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8277190474 / 1000000000000) (-8277190473 / 1000000000000), orderedInterval (-48756579705 / 1000000000000) (-48756579704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1846459197080017 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20531675492 / 1000000000000) (-20531675491 / 1000000000000), orderedInterval (-30922313932 / 1000000000000) (-30922313931 / 1000000000000)))) (orderedInterval (-22353317384 / 1000000000000) (-22353279908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1725201698299573 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38158731101 / 1000000000000) (-38158729691 / 1000000000000), orderedInterval (4511617928 / 1000000000000) (4511619337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1231185336711109 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29480262931 / 1000000000000) (29480262932 / 1000000000000), orderedInterval (34582004403 / 1000000000000) (34582004404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1396032950900211 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37596937236 / 1000000000000) (-37596937235 / 1000000000000), orderedInterval (-20208211710 / 1000000000000) (-20208211709 / 1000000000000)))) (orderedInterval (4998064276 / 1000000000000) (4998064370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1163866730709059 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18922108254 / 1000000000000) (18922108886 / 1000000000000), orderedInterval (-42809885116 / 1000000000000) (-42809884484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1028311553118239 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12417755706 / 1000000000000) (12417755707 / 1000000000000), orderedInterval (48164775235 / 1000000000000) (48164775236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (298044768461661 / 800000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20125975680 / 1000000000000) (20125976844 / 1000000000000), orderedInterval (-36134289490 / 1000000000000) (-36134288326 / 1000000000000)))) (orderedInterval (-5940985404 / 1000000000000) (-5940985310 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks1_2 :
    compactCertificate329.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (824407514801767 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24596013792 / 1000000000000) (-24596012064 / 1000000000000), orderedInterval (49898421332 / 1000000000000) (49898423060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (698859380360687 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25145159503 / 1000000000000) (-25145158015 / 1000000000000), orderedInterval (54949052411 / 1000000000000) (54949053900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (437313751148261 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11927445856 / 1000000000000) (-11927445855 / 1000000000000), orderedInterval (-75316511233 / 1000000000000) (-75316511231 / 1000000000000)))) (orderedInterval (-12187643433 / 1000000000000) (-12187643030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (235188789807387 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11401068631 / 1000000000000) (11401068679 / 1000000000000), orderedInterval (-103527020850 / 1000000000000) (-103527020802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (638583315063161 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13115582093 / 1000000000000) (-13115582092 / 1000000000000), orderedInterval (-61730275933 / 1000000000000) (-61730275932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (871930922551897 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-49192361151 / 1000000000000) (-49192348964 / 1000000000000), orderedInterval (22487203865 / 1000000000000) (22487216052 / 1000000000000)))) (orderedInterval (-196986243 / 1000000000000) (-196985210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (368686248851739 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79902175189 / 1000000000000) (-79902173918 / 1000000000000), orderedInterval (23290733628 / 1000000000000) (23290734899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1498689132733819 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41192327548 / 1000000000000) (-41192327171 / 1000000000000), orderedInterval (1580840971 / 1000000000000) (1580841348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1001054885321621 / 4000000000000) 1 (IntervalRat.scale (403 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13879723572 / 1000000000000) (-13879723435 / 1000000000000), orderedInterval (48516422097 / 1000000000000) (48516422234 / 1000000000000)))) (orderedInterval (-11480969714 / 1000000000000) (-11480969543 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks1 :
    compactCertificate329.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate329.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate329_chunkChecks1_0
    compactCertificate329_chunkChecks1_1 compactCertificate329_chunkChecks1_2

theorem compactCertificate329_chunkChecks2_0 :
    compactCertificate329.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (403 / 2) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52840147774 / 1000000000000) (52840147775 / 1000000000000), orderedInterval (19034338551 / 1000000000000) (19034338552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (593695952004103 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65482195168 / 1000000000000) (-65482195131 / 1000000000000), orderedInterval (-899733218 / 1000000000000) (-899733182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (191989072624999 / 800000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46612488402 / 1000000000000) (46612503741 / 1000000000000), orderedInterval (-22006135333 / 1000000000000) (-22006119994 / 1000000000000)))) (orderedInterval (-24522633554 / 1000000000000) (-24522632253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (173238998096021 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13304918440 / 1000000000000) (13304918442 / 1000000000000), orderedInterval (120358491679 / 1000000000000) (120358491681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (465344316966737 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57084315456 / 1000000000000) (-57084315455 / 1000000000000), orderedInterval (-46803768303 / 1000000000000) (-46803768302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1263500342926029 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26837819018 / 1000000000000) (26837825836 / 1000000000000), orderedInterval (-36030652758 / 1000000000000) (-36030645941 / 1000000000000)))) (orderedInterval (5376282995 / 1000000000000) (5376284229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (930688633933877 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43417178833 / 1000000000000) (43417178834 / 1000000000000), orderedInterval (29079798925 / 1000000000000) (29079798926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1594750837325321 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18824700254 / 1000000000000) (-18824700253 / 1000000000000), orderedInterval (-35224362074 / 1000000000000) (-35224362073 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1174686248851739 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35076684340 / 1000000000000) (-35076627812 / 1000000000000), orderedInterval (30677052727 / 1000000000000) (30677109254 / 1000000000000)))) (orderedInterval (-488444879 / 1000000000000) (-488441931 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks2_1 :
    compactCertificate329.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1802270789864597 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32350553469 / 1000000000000) (-32350459568 / 1000000000000), orderedInterval (19176707050 / 1000000000000) (19176800951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1040541525680813 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8277190474 / 1000000000000) (-8277190473 / 1000000000000), orderedInterval (-48756579705 / 1000000000000) (-48756579704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1846459197080017 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20531675492 / 1000000000000) (-20531675491 / 1000000000000), orderedInterval (-30922313932 / 1000000000000) (-30922313931 / 1000000000000)))) (orderedInterval (-12290582158 / 1000000000000) (-12290498191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1725201698299573 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38158731101 / 1000000000000) (-38158729691 / 1000000000000), orderedInterval (4511617928 / 1000000000000) (4511619337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1231185336711109 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29480262931 / 1000000000000) (29480262932 / 1000000000000), orderedInterval (34582004403 / 1000000000000) (34582004404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1396032950900211 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37596937236 / 1000000000000) (-37596937235 / 1000000000000), orderedInterval (-20208211710 / 1000000000000) (-20208211709 / 1000000000000)))) (orderedInterval (-10256444337 / 1000000000000) (-10256444154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1163866730709059 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18922108254 / 1000000000000) (18922108886 / 1000000000000), orderedInterval (-42809885116 / 1000000000000) (-42809884484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1028311553118239 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12417755706 / 1000000000000) (12417755707 / 1000000000000), orderedInterval (48164775235 / 1000000000000) (48164775236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (298044768461661 / 800000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20125975680 / 1000000000000) (20125976844 / 1000000000000), orderedInterval (-36134289490 / 1000000000000) (-36134288326 / 1000000000000)))) (orderedInterval (-1030990669 / 1000000000000) (-1030990509 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks2_2 :
    compactCertificate329.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (824407514801767 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24596013792 / 1000000000000) (-24596012064 / 1000000000000), orderedInterval (49898421332 / 1000000000000) (49898423060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (698859380360687 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25145159503 / 1000000000000) (-25145158015 / 1000000000000), orderedInterval (54949052411 / 1000000000000) (54949053900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (437313751148261 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11927445856 / 1000000000000) (-11927445855 / 1000000000000), orderedInterval (-75316511233 / 1000000000000) (-75316511231 / 1000000000000)))) (orderedInterval (-5009595496 / 1000000000000) (-5009595097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (235188789807387 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11401068631 / 1000000000000) (11401068679 / 1000000000000), orderedInterval (-103527020850 / 1000000000000) (-103527020802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (638583315063161 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13115582093 / 1000000000000) (-13115582092 / 1000000000000), orderedInterval (-61730275933 / 1000000000000) (-61730275932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (871930922551897 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-49192361151 / 1000000000000) (-49192348964 / 1000000000000), orderedInterval (22487203865 / 1000000000000) (22487216052 / 1000000000000)))) (orderedInterval (-4579930107 / 1000000000000) (-4579928987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (368686248851739 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79902175189 / 1000000000000) (-79902173918 / 1000000000000), orderedInterval (23290733628 / 1000000000000) (23290734899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1498689132733819 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41192327548 / 1000000000000) (-41192327171 / 1000000000000), orderedInterval (1580840971 / 1000000000000) (1580841348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1001054885321621 / 4000000000000) 2 (IntervalRat.scale (403 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13879723572 / 1000000000000) (-13879723435 / 1000000000000), orderedInterval (48516422097 / 1000000000000) (48516422234 / 1000000000000)))) (orderedInterval (-15452609694 / 1000000000000) (-15452609430 / 1000000000000))) = true
  rfl'

theorem compactCertificate329_chunkChecks2 :
    compactCertificate329.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate329.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate329_chunkChecks2_0
    compactCertificate329_chunkChecks2_1 compactCertificate329_chunkChecks2_2

theorem compactCertificate329_chunkChecks3_0 :
    compactCertificate329.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (403 / 2) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52840147774 / 1000000000000) (52840147775 / 1000000000000), orderedInterval (19034338551 / 1000000000000) (19034338552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (593695952004103 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65482195168 / 1000000000000) (-65482195131 / 1000000000000), orderedInterval (-899733218 / 1000000000000) (-899733182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (191989072624999 / 800000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46612488402 / 1000000000000) (46612503741 / 1000000000000), orderedInterval (-22006135333 / 1000000000000) (-22006119994 / 1000000000000)))) (orderedInterval (-5237740054 / 1000000000000) (-5237738505 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (173238998096021 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13304918440 / 1000000000000) (13304918442 / 1000000000000), orderedInterval (120358491679 / 1000000000000) (120358491681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (465344316966737 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57084315456 / 1000000000000) (-57084315455 / 1000000000000), orderedInterval (-46803768303 / 1000000000000) (-46803768302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1263500342926029 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26837819018 / 1000000000000) (26837825836 / 1000000000000), orderedInterval (-36030652758 / 1000000000000) (-36030645941 / 1000000000000)))) (orderedInterval (-9552096696 / 1000000000000) (-9552094765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (930688633933877 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43417178833 / 1000000000000) (43417178834 / 1000000000000), orderedInterval (29079798925 / 1000000000000) (29079798926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1594750837325321 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18824700254 / 1000000000000) (-18824700253 / 1000000000000), orderedInterval (-35224362074 / 1000000000000) (-35224362073 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1174686248851739 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35076684340 / 1000000000000) (-35076627812 / 1000000000000), orderedInterval (30677052727 / 1000000000000) (30677109254 / 1000000000000)))) (orderedInterval (-10708315008 / 1000000000000) (-10708310700 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate329_chunkChecks3_1 :
    compactCertificate329.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1802270789864597 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32350553469 / 1000000000000) (-32350459568 / 1000000000000), orderedInterval (19176707050 / 1000000000000) (19176800951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1040541525680813 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8277190474 / 1000000000000) (-8277190473 / 1000000000000), orderedInterval (-48756579705 / 1000000000000) (-48756579704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1846459197080017 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20531675492 / 1000000000000) (-20531675491 / 1000000000000), orderedInterval (-30922313932 / 1000000000000) (-30922313931 / 1000000000000)))) (orderedInterval (98780603586 / 1000000000000) (98780791322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1725201698299573 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38158731101 / 1000000000000) (-38158729691 / 1000000000000), orderedInterval (4511617928 / 1000000000000) (4511619337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1231185336711109 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29480262931 / 1000000000000) (29480262932 / 1000000000000), orderedInterval (34582004403 / 1000000000000) (34582004404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1396032950900211 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37596937236 / 1000000000000) (-37596937235 / 1000000000000), orderedInterval (-20208211710 / 1000000000000) (-20208211709 / 1000000000000)))) (orderedInterval (-11337270912 / 1000000000000) (-11337270552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1163866730709059 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18922108254 / 1000000000000) (18922108886 / 1000000000000), orderedInterval (-42809885116 / 1000000000000) (-42809884484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1028311553118239 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12417755706 / 1000000000000) (12417755707 / 1000000000000), orderedInterval (48164775235 / 1000000000000) (48164775236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (298044768461661 / 800000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20125975680 / 1000000000000) (20125976844 / 1000000000000), orderedInterval (-36134289490 / 1000000000000) (-36134288326 / 1000000000000)))) (orderedInterval (13064992920 / 1000000000000) (13064993195 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate329_chunkChecks3_2 :
    compactCertificate329.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (824407514801767 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24596013792 / 1000000000000) (-24596012064 / 1000000000000), orderedInterval (49898421332 / 1000000000000) (49898423060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (698859380360687 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25145159503 / 1000000000000) (-25145158015 / 1000000000000), orderedInterval (54949052411 / 1000000000000) (54949053900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (437313751148261 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11927445856 / 1000000000000) (-11927445855 / 1000000000000), orderedInterval (-75316511233 / 1000000000000) (-75316511231 / 1000000000000)))) (orderedInterval (10981198345 / 1000000000000) (10981198741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (235188789807387 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11401068631 / 1000000000000) (11401068679 / 1000000000000), orderedInterval (-103527020850 / 1000000000000) (-103527020802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (638583315063161 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13115582093 / 1000000000000) (-13115582092 / 1000000000000), orderedInterval (-61730275933 / 1000000000000) (-61730275932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (871930922551897 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-49192361151 / 1000000000000) (-49192348964 / 1000000000000), orderedInterval (22487203865 / 1000000000000) (22487216052 / 1000000000000)))) (orderedInterval (1460584356 / 1000000000000) (1460585567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (368686248851739 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79902175189 / 1000000000000) (-79902173918 / 1000000000000), orderedInterval (23290733628 / 1000000000000) (23290734899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1498689132733819 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41192327548 / 1000000000000) (-41192327171 / 1000000000000), orderedInterval (1580840971 / 1000000000000) (1580841348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1001054885321621 / 4000000000000) 3 (IntervalRat.scale (403 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13879723572 / 1000000000000) (-13879723435 / 1000000000000), orderedInterval (48516422097 / 1000000000000) (48516422234 / 1000000000000)))) (orderedInterval (18330448468 / 1000000000000) (18330448895 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate329_chunkChecks3 :
    compactCertificate329.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate329.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate329_chunkChecks3_0
    compactCertificate329_chunkChecks3_1 compactCertificate329_chunkChecks3_2

theorem compactCertificate329_chunkChecks4_0 :
    compactCertificate329.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (403 / 2) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52840147774 / 1000000000000) (52840147775 / 1000000000000), orderedInterval (19034338551 / 1000000000000) (19034338552 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (593695952004103 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-65482195168 / 1000000000000) (-65482195131 / 1000000000000), orderedInterval (-899733218 / 1000000000000) (-899733182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (191989072624999 / 800000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46612488402 / 1000000000000) (46612503741 / 1000000000000), orderedInterval (-22006135333 / 1000000000000) (-22006119994 / 1000000000000)))) (orderedInterval (26319341586 / 1000000000000) (26319343438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (173238998096021 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (13304918440 / 1000000000000) (13304918442 / 1000000000000), orderedInterval (120358491679 / 1000000000000) (120358491681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (465344316966737 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57084315456 / 1000000000000) (-57084315455 / 1000000000000), orderedInterval (-46803768303 / 1000000000000) (-46803768302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1263500342926029 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26837819018 / 1000000000000) (26837825836 / 1000000000000), orderedInterval (-36030652758 / 1000000000000) (-36030645941 / 1000000000000)))) (orderedInterval (-11658606240 / 1000000000000) (-11658603206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (930688633933877 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43417178833 / 1000000000000) (43417178834 / 1000000000000), orderedInterval (29079798925 / 1000000000000) (29079798926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1594750837325321 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18824700254 / 1000000000000) (-18824700253 / 1000000000000), orderedInterval (-35224362074 / 1000000000000) (-35224362073 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1174686248851739 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35076684340 / 1000000000000) (-35076627812 / 1000000000000), orderedInterval (30677052727 / 1000000000000) (30677109254 / 1000000000000)))) (orderedInterval (5180257483 / 1000000000000) (5180263807 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate329_chunkChecks4_1 :
    compactCertificate329.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1802270789864597 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32350553469 / 1000000000000) (-32350459568 / 1000000000000), orderedInterval (19176707050 / 1000000000000) (19176800951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1040541525680813 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8277190474 / 1000000000000) (-8277190473 / 1000000000000), orderedInterval (-48756579705 / 1000000000000) (-48756579704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1846459197080017 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20531675492 / 1000000000000) (-20531675491 / 1000000000000), orderedInterval (-30922313932 / 1000000000000) (-30922313931 / 1000000000000)))) (orderedInterval (60631767837 / 1000000000000) (60632188541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1725201698299573 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38158731101 / 1000000000000) (-38158729691 / 1000000000000), orderedInterval (4511617928 / 1000000000000) (4511619337 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1231185336711109 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29480262931 / 1000000000000) (29480262932 / 1000000000000), orderedInterval (34582004403 / 1000000000000) (34582004404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1396032950900211 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37596937236 / 1000000000000) (-37596937235 / 1000000000000), orderedInterval (-20208211710 / 1000000000000) (-20208211709 / 1000000000000)))) (orderedInterval (31462200734 / 1000000000000) (31462201462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1163866730709059 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (18922108254 / 1000000000000) (18922108886 / 1000000000000), orderedInterval (-42809885116 / 1000000000000) (-42809884484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1028311553118239 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (12417755706 / 1000000000000) (12417755707 / 1000000000000), orderedInterval (48164775235 / 1000000000000) (48164775236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (298044768461661 / 800000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20125975680 / 1000000000000) (20125976844 / 1000000000000), orderedInterval (-36134289490 / 1000000000000) (-36134288326 / 1000000000000)))) (orderedInterval (4959391199 / 1000000000000) (4959391683 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate329_chunkChecks4_2 :
    compactCertificate329.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (824407514801767 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24596013792 / 1000000000000) (-24596012064 / 1000000000000), orderedInterval (49898421332 / 1000000000000) (49898423060 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (698859380360687 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25145159503 / 1000000000000) (-25145158015 / 1000000000000), orderedInterval (54949052411 / 1000000000000) (54949053900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (437313751148261 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11927445856 / 1000000000000) (-11927445855 / 1000000000000), orderedInterval (-75316511233 / 1000000000000) (-75316511231 / 1000000000000)))) (orderedInterval (4966140025 / 1000000000000) (4966140421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (235188789807387 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11401068631 / 1000000000000) (11401068679 / 1000000000000), orderedInterval (-103527020850 / 1000000000000) (-103527020802 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (638583315063161 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-13115582093 / 1000000000000) (-13115582092 / 1000000000000), orderedInterval (-61730275933 / 1000000000000) (-61730275932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (871930922551897 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-49192361151 / 1000000000000) (-49192348964 / 1000000000000), orderedInterval (22487203865 / 1000000000000) (22487216052 / 1000000000000)))) (orderedInterval (5264496775 / 1000000000000) (5264498089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (368686248851739 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-79902175189 / 1000000000000) (-79902173918 / 1000000000000), orderedInterval (23290733628 / 1000000000000) (23290734899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1498689132733819 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41192327548 / 1000000000000) (-41192327171 / 1000000000000), orderedInterval (1580840971 / 1000000000000) (1580841348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1001054885321621 / 4000000000000) 4 (IntervalRat.scale (403 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13879723572 / 1000000000000) (-13879723435 / 1000000000000), orderedInterval (48516422097 / 1000000000000) (48516422234 / 1000000000000)))) (orderedInterval (46076013986 / 1000000000000) (46076014704 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate329_chunkChecks4 :
    compactCertificate329.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate329.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate329_chunkChecks4_0
    compactCertificate329_chunkChecks4_1 compactCertificate329_chunkChecks4_2

theorem compactCertificate329_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate329.chunkCheck r b = true :=
  compactCertificate329.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate329_chunkChecks0
    · exact compactCertificate329_chunkChecks1
    · exact compactCertificate329_chunkChecks2
    · exact compactCertificate329_chunkChecks3
    · exact compactCertificate329_chunkChecks4)

theorem compactCertificate329_coefficient0 :
    compactCertificate329.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate329_coefficient1 :
    compactCertificate329.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate329_coefficient2 :
    compactCertificate329.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate329_coefficient3 :
    compactCertificate329.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate329_coefficient4 :
    compactCertificate329.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate329_coefficients : ∀ r : Fin 5,
    compactCertificate329.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate329_coefficient0
  · exact compactCertificate329_coefficient1
  · exact compactCertificate329_coefficient2
  · exact compactCertificate329_coefficient3
  · exact compactCertificate329_coefficient4

theorem compactCertificate329_lower : (1 : ℚ) ≤ compactCertificate329.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate329, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate329_proves {t : ℝ} (ht : t ∈ compactCertificate329.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate329.proves compactCertificate329_states compactCertificate329_chunks
    compactCertificate329_coefficients compactCertificate329_lower ht

end Erdos232
