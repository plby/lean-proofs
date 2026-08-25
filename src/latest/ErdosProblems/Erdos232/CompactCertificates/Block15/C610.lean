/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate610 : CompactCertificate where
  left := 481
  right := 482
  center := 963 / 2
  grid := fun i =>
    match i.val with
    | 0 => 153
    | 1 => 113
    | 2 => 183
    | 3 => 33
    | 4 => 89
    | 5 => 240
    | 6 => 177
    | 7 => 303
    | 8 => 223
    | 9 => 343
    | 10 => 198
    | 11 => 351
    | 12 => 328
    | 13 => 234
    | 14 => 266
    | 15 => 221
    | 16 => 196
    | 17 => 284
    | 18 => 157
    | 19 => 133
    | 20 => 83
    | 21 => 45
    | 22 => 121
    | 23 => 166
    | 24 => 70
    | 25 => 285
    | _ => 190
  point := fun i =>
    match i.val with
    | 0 => 963 / 2
    | 1 => 1418682882828663 / 4000000000000
    | 2 => 458772895627479 / 800000000000
    | 3 => 413968126963941 / 4000000000000
    | 4 => 1111976618458977 / 4000000000000
    | 5 => 3019232829374109 / 4000000000000
    | 6 => 2223953236918917 / 4000000000000
    | 7 => 3810781777529241 / 4000000000000
    | 8 => 2807004609539019 / 4000000000000
    | 9 => 4306666924664037 / 4000000000000
    | 10 => 2486455308264573 / 4000000000000
    | 11 => 4412258577637857 / 4000000000000
    | 12 => 4122504306358533 / 4000000000000
    | 13 => 2942013596160789 / 4000000000000
    | 14 => 3335929855376931 / 4000000000000
    | 15 => 2781150525242739 / 4000000000000
    | 16 => 2457230832885519 / 4000000000000
    | 17 => 712201270542381 / 800000000000
    | 18 => 1969986195419607 / 4000000000000
    | 19 => 1669979114856927 / 4000000000000
    | 20 => 1044995390460981 / 4000000000000
    | 21 => 562001996487627 / 4000000000000
    | 22 => 1525944745423881 / 4000000000000
    | 23 => 2083547092847337 / 4000000000000
    | 24 => 881004609539019 / 4000000000000
    | 25 => 3581234825862699 / 4000000000000
    | _ => 2392098894701541 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36314839876 / 1000000000000) (-36314839001 / 1000000000000), orderedInterval (1879222751 / 1000000000000) (1879223626 / 1000000000000))
    | 1 => (orderedInterval (-18648985956 / 1000000000000) (-18648985955 / 1000000000000), orderedInterval (-38015482044 / 1000000000000) (-38015482043 / 1000000000000))
    | 2 => (orderedInterval (20432266367 / 1000000000000) (20432268432 / 1000000000000), orderedInterval (-26336036908 / 1000000000000) (-26336034842 / 1000000000000))
    | 3 => (orderedInterval (-44522013269 / 1000000000000) (-44522013268 / 1000000000000), orderedInterval (-64354288427 / 1000000000000) (-64354288426 / 1000000000000))
    | 4 => (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))
    | 5 => (orderedInterval (29017971162 / 1000000000000) (29017974918 / 1000000000000), orderedInterval (-1192383660 / 1000000000000) (-1192379904 / 1000000000000))
    | 6 => (orderedInterval (-22097467624 / 1000000000000) (-22097467623 / 1000000000000), orderedInterval (-25606786926 / 1000000000000) (-25606786925 / 1000000000000))
    | 7 => (orderedInterval (-25849452406 / 1000000000000) (-25849444813 / 1000000000000), orderedInterval (203326224 / 1000000000000) (203333817 / 1000000000000))
    | 8 => (orderedInterval (-27853134798 / 1000000000000) (-27853053141 / 1000000000000), orderedInterval (11482451560 / 1000000000000) (11482533217 / 1000000000000))
    | 9 => (orderedInterval (2772518966 / 1000000000000) (2772518967 / 1000000000000), orderedInterval (-24159120222 / 1000000000000) (-24159120221 / 1000000000000))
    | 10 => (orderedInterval (11383650035 / 1000000000000) (11383650036 / 1000000000000), orderedInterval (29899923385 / 1000000000000) (29899923386 / 1000000000000))
    | 11 => (orderedInterval (-21936849964 / 1000000000000) (-21936849847 / 1000000000000), orderedInterval (-9783518386 / 1000000000000) (-9783518269 / 1000000000000))
    | 12 => (orderedInterval (20486808176 / 1000000000000) (20486808181 / 1000000000000), orderedInterval (14061047048 / 1000000000000) (14061047052 / 1000000000000))
    | 13 => (orderedInterval (26924810980 / 1000000000000) (26924810988 / 1000000000000), orderedInterval (11839645231 / 1000000000000) (11839645238 / 1000000000000))
    | 14 => (orderedInterval (-21572348550 / 1000000000000) (-21572342232 / 1000000000000), orderedInterval (17275114006 / 1000000000000) (17275120324 / 1000000000000))
    | 15 => (orderedInterval (-29593976555 / 1000000000000) (-29593961024 / 1000000000000), orderedInterval (6331386339 / 1000000000000) (6331401870 / 1000000000000))
    | 16 => (orderedInterval (-19718519345 / 1000000000000) (-19718517729 / 1000000000000), orderedInterval (25462085100 / 1000000000000) (25462086716 / 1000000000000))
    | 17 => (orderedInterval (-24678842004 / 1000000000000) (-24678774781 / 1000000000000), orderedInterval (10312237411 / 1000000000000) (10312304634 / 1000000000000))
    | 18 => (orderedInterval (-1856038462 / 1000000000000) (-1856038461 / 1000000000000), orderedInterval (-35903460989 / 1000000000000) (-35903460988 / 1000000000000))
    | 19 => (orderedInterval (-16916705771 / 1000000000000) (-16916705770 / 1000000000000), orderedInterval (-35174663136 / 1000000000000) (-35174663135 / 1000000000000))
    | 20 => (orderedInterval (-47313988814 / 1000000000000) (-47313988812 / 1000000000000), orderedInterval (-13988351984 / 1000000000000) (-13988351983 / 1000000000000))
    | 21 => (orderedInterval (5826176093 / 1000000000000) (5826176111 / 1000000000000), orderedInterval (-67081671487 / 1000000000000) (-67081671469 / 1000000000000))
    | 22 => (orderedInterval (-34441890447 / 1000000000000) (-34441797730 / 1000000000000), orderedInterval (22012051087 / 1000000000000) (22012143803 / 1000000000000))
    | 23 => (orderedInterval (5830169142 / 1000000000000) (5830169143 / 1000000000000), orderedInterval (34464596838 / 1000000000000) (34464596839 / 1000000000000))
    | 24 => (orderedInterval (48496607803 / 1000000000000) (48496607804 / 1000000000000), orderedInterval (23095528442 / 1000000000000) (23095528443 / 1000000000000))
    | 25 => (orderedInterval (-17981542106 / 1000000000000) (-17981542105 / 1000000000000), orderedInterval (-19680714626 / 1000000000000) (-19680714625 / 1000000000000))
    | _ => (orderedInterval (30797233453 / 1000000000000) (30797265461 / 1000000000000), orderedInterval (-10799188406 / 1000000000000) (-10799156398 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13368714957 / 1000000000000) (-13368714455 / 1000000000000)
      | 1 => orderedInterval (-299207114 / 1000000000000) (-299205097 / 1000000000000)
      | 2 => orderedInterval (124144974 / 1000000000000) (124147209 / 1000000000000)
      | 3 => orderedInterval (-2767660923 / 1000000000000) (-2767660716 / 1000000000000)
      | 4 => orderedInterval (2285405631 / 1000000000000) (2285405722 / 1000000000000)
      | 5 => orderedInterval (154807910 / 1000000000000) (154809949 / 1000000000000)
      | 6 => orderedInterval (-286068464 / 1000000000000) (-286068343 / 1000000000000)
      | 7 => orderedInterval (226977685 / 1000000000000) (226979846 / 1000000000000)
      | _ => orderedInterval (-4022301087 / 1000000000000) (-4022294948 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1356670844 / 1000000000000) (-1356670315 / 1000000000000)
      | 1 => orderedInterval (-404637639 / 1000000000000) (-404636178 / 1000000000000)
      | 2 => orderedInterval (392038911 / 1000000000000) (392042297 / 1000000000000)
      | 3 => orderedInterval (9272807824 / 1000000000000) (9272808258 / 1000000000000)
      | 4 => orderedInterval (1015440840 / 1000000000000) (1015440990 / 1000000000000)
      | 5 => orderedInterval (-1265261062 / 1000000000000) (-1265257436 / 1000000000000)
      | 6 => orderedInterval (7350952278 / 1000000000000) (7350952390 / 1000000000000)
      | 7 => orderedInterval (-2891605115 / 1000000000000) (-2891603396 / 1000000000000)
      | _ => orderedInterval (5559112200 / 1000000000000) (5559119846 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12790292072 / 1000000000000) (12790292635 / 1000000000000)
      | 1 => orderedInterval (4621015613 / 1000000000000) (4621016927 / 1000000000000)
      | 2 => orderedInterval (-1692288797 / 1000000000000) (-1692283597 / 1000000000000)
      | 3 => orderedInterval (17404455840 / 1000000000000) (17404456775 / 1000000000000)
      | 4 => orderedInterval (-4576008867 / 1000000000000) (-4576008614 / 1000000000000)
      | 5 => orderedInterval (1038497586 / 1000000000000) (1038504101 / 1000000000000)
      | 6 => orderedInterval (-592144754 / 1000000000000) (-592144647 / 1000000000000)
      | 7 => orderedInterval (47586467 / 1000000000000) (47587843 / 1000000000000)
      | _ => orderedInterval (3780113741 / 1000000000000) (3780123297 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1981001446 / 1000000000000) (1981002050 / 1000000000000)
      | 1 => orderedInterval (-113881768 / 1000000000000) (-113880275 / 1000000000000)
      | 2 => orderedInterval (-806997546 / 1000000000000) (-806989459 / 1000000000000)
      | 3 => orderedInterval (-36076089694 / 1000000000000) (-36076087634 / 1000000000000)
      | 4 => orderedInterval (-1037371431 / 1000000000000) (-1037371001 / 1000000000000)
      | 5 => orderedInterval (1134816056 / 1000000000000) (1134827833 / 1000000000000)
      | 6 => orderedInterval (-7366870759 / 1000000000000) (-7366870656 / 1000000000000)
      | 7 => orderedInterval (3561451965 / 1000000000000) (3561453067 / 1000000000000)
      | _ => orderedInterval (-14202357236 / 1000000000000) (-14202345284 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-12040795847 / 1000000000000) (-12040795195 / 1000000000000)
      | 1 => orderedInterval (-12313792570 / 1000000000000) (-12313790554 / 1000000000000)
      | 2 => orderedInterval (9185710672 / 1000000000000) (9185723479 / 1000000000000)
      | 3 => orderedInterval (-95716292640 / 1000000000000) (-95716288051 / 1000000000000)
      | 4 => orderedInterval (7085558866 / 1000000000000) (7085559614 / 1000000000000)
      | 5 => orderedInterval (-5884918212 / 1000000000000) (-5884896784 / 1000000000000)
      | 6 => orderedInterval (763119934 / 1000000000000) (763120036 / 1000000000000)
      | 7 => orderedInterval (-319640080 / 1000000000000) (-319639191 / 1000000000000)
      | _ => orderedInterval (3819095777 / 1000000000000) (3819110801 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17952616345 / 1000000000000) (-17952600833 / 1000000000000)
    | 1 => orderedInterval (17672177393 / 1000000000000) (17672196456 / 1000000000000)
    | 2 => orderedInterval (32821518901 / 1000000000000) (32821544720 / 1000000000000)
    | 3 => orderedInterval (-52926298967 / 1000000000000) (-52926261359 / 1000000000000)
    | _ => orderedInterval (-105421954100 / 1000000000000) (-105421895845 / 1000000000000)

theorem compactCertificate610_stateChecks0 :
    compactCertificate610.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (963 / 2)) (orderedInterval (-36314839876 / 1000000000000) (-36314839001 / 1000000000000), orderedInterval (1879222751 / 1000000000000) (1879223626 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1418682882828663 / 4000000000000)) (orderedInterval (-18648985956 / 1000000000000) (-18648985955 / 1000000000000), orderedInterval (-38015482044 / 1000000000000) (-38015482043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (458772895627479 / 800000000000)) (orderedInterval (20432266367 / 1000000000000) (20432268432 / 1000000000000), orderedInterval (-26336036908 / 1000000000000) (-26336034842 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks1 :
    compactCertificate610.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (413968126963941 / 4000000000000)) (orderedInterval (-44522013269 / 1000000000000) (-44522013268 / 1000000000000), orderedInterval (-64354288427 / 1000000000000) (-64354288426 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1111976618458977 / 4000000000000)) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3019232829374109 / 4000000000000)) (orderedInterval (29017971162 / 1000000000000) (29017974918 / 1000000000000), orderedInterval (-1192383660 / 1000000000000) (-1192379904 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks2 :
    compactCertificate610.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2223953236918917 / 4000000000000)) (orderedInterval (-22097467624 / 1000000000000) (-22097467623 / 1000000000000), orderedInterval (-25606786926 / 1000000000000) (-25606786925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 303 12 (3810781777529241 / 4000000000000)) (orderedInterval (-25849452406 / 1000000000000) (-25849444813 / 1000000000000), orderedInterval (203326224 / 1000000000000) (203333817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2807004609539019 / 4000000000000)) (orderedInterval (-27853134798 / 1000000000000) (-27853053141 / 1000000000000), orderedInterval (11482451560 / 1000000000000) (11482533217 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks3 :
    compactCertificate610.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 343 12 (4306666924664037 / 4000000000000)) (orderedInterval (2772518966 / 1000000000000) (2772518967 / 1000000000000), orderedInterval (-24159120222 / 1000000000000) (-24159120221 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2486455308264573 / 4000000000000)) (orderedInterval (11383650035 / 1000000000000) (11383650036 / 1000000000000), orderedInterval (29899923385 / 1000000000000) (29899923386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 351 12 (4412258577637857 / 4000000000000)) (orderedInterval (-21936849964 / 1000000000000) (-21936849847 / 1000000000000), orderedInterval (-9783518386 / 1000000000000) (-9783518269 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks4 :
    compactCertificate610.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 328 12 (4122504306358533 / 4000000000000)) (orderedInterval (20486808176 / 1000000000000) (20486808181 / 1000000000000), orderedInterval (14061047048 / 1000000000000) (14061047052 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2942013596160789 / 4000000000000)) (orderedInterval (26924810980 / 1000000000000) (26924810988 / 1000000000000), orderedInterval (11839645231 / 1000000000000) (11839645238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3335929855376931 / 4000000000000)) (orderedInterval (-21572348550 / 1000000000000) (-21572342232 / 1000000000000), orderedInterval (17275114006 / 1000000000000) (17275120324 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks5 :
    compactCertificate610.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2781150525242739 / 4000000000000)) (orderedInterval (-29593976555 / 1000000000000) (-29593961024 / 1000000000000), orderedInterval (6331386339 / 1000000000000) (6331401870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2457230832885519 / 4000000000000)) (orderedInterval (-19718519345 / 1000000000000) (-19718517729 / 1000000000000), orderedInterval (25462085100 / 1000000000000) (25462086716 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (712201270542381 / 800000000000)) (orderedInterval (-24678842004 / 1000000000000) (-24678774781 / 1000000000000), orderedInterval (10312237411 / 1000000000000) (10312304634 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks6 :
    compactCertificate610.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1969986195419607 / 4000000000000)) (orderedInterval (-1856038462 / 1000000000000) (-1856038461 / 1000000000000), orderedInterval (-35903460989 / 1000000000000) (-35903460988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1669979114856927 / 4000000000000)) (orderedInterval (-16916705771 / 1000000000000) (-16916705770 / 1000000000000), orderedInterval (-35174663136 / 1000000000000) (-35174663135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1044995390460981 / 4000000000000)) (orderedInterval (-47313988814 / 1000000000000) (-47313988812 / 1000000000000), orderedInterval (-13988351984 / 1000000000000) (-13988351983 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks7 :
    compactCertificate610.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (562001996487627 / 4000000000000)) (orderedInterval (5826176093 / 1000000000000) (5826176111 / 1000000000000), orderedInterval (-67081671487 / 1000000000000) (-67081671469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1525944745423881 / 4000000000000)) (orderedInterval (-34441890447 / 1000000000000) (-34441797730 / 1000000000000), orderedInterval (22012051087 / 1000000000000) (22012143803 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2083547092847337 / 4000000000000)) (orderedInterval (5830169142 / 1000000000000) (5830169143 / 1000000000000), orderedInterval (34464596838 / 1000000000000) (34464596839 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_stateChecks8 :
    compactCertificate610.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (881004609539019 / 4000000000000)) (orderedInterval (48496607803 / 1000000000000) (48496607804 / 1000000000000), orderedInterval (23095528442 / 1000000000000) (23095528443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (3581234825862699 / 4000000000000)) (orderedInterval (-17981542106 / 1000000000000) (-17981542105 / 1000000000000), orderedInterval (-19680714626 / 1000000000000) (-19680714625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2392098894701541 / 4000000000000)) (orderedInterval (30797233453 / 1000000000000) (30797265461 / 1000000000000), orderedInterval (-10799188406 / 1000000000000) (-10799156398 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_states : ∀ j,
    BesselStateValid (compactCertificate610.point j) (compactCertificate610.state j) :=
  compactCertificate610.statesValid_of_checks3 compactCertificate610_stateChecks0
    compactCertificate610_stateChecks1 compactCertificate610_stateChecks2
    compactCertificate610_stateChecks3 compactCertificate610_stateChecks4
    compactCertificate610_stateChecks5 compactCertificate610_stateChecks6
    compactCertificate610_stateChecks7 compactCertificate610_stateChecks8

theorem compactCertificate610_chunkChecks0_0 :
    compactCertificate610.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (963 / 2) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36314839876 / 1000000000000) (-36314839001 / 1000000000000), orderedInterval (1879222751 / 1000000000000) (1879223626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1418682882828663 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18648985956 / 1000000000000) (-18648985955 / 1000000000000), orderedInterval (-38015482044 / 1000000000000) (-38015482043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (458772895627479 / 800000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20432266367 / 1000000000000) (20432268432 / 1000000000000), orderedInterval (-26336036908 / 1000000000000) (-26336034842 / 1000000000000)))) (orderedInterval (-13368714957 / 1000000000000) (-13368714455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (413968126963941 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44522013269 / 1000000000000) (-44522013268 / 1000000000000), orderedInterval (-64354288427 / 1000000000000) (-64354288426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3019232829374109 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29017971162 / 1000000000000) (29017974918 / 1000000000000), orderedInterval (-1192383660 / 1000000000000) (-1192379904 / 1000000000000)))) (orderedInterval (-299207114 / 1000000000000) (-299205097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2223953236918917 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22097467624 / 1000000000000) (-22097467623 / 1000000000000), orderedInterval (-25606786926 / 1000000000000) (-25606786925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3810781777529241 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25849452406 / 1000000000000) (-25849444813 / 1000000000000), orderedInterval (203326224 / 1000000000000) (203333817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2807004609539019 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27853134798 / 1000000000000) (-27853053141 / 1000000000000), orderedInterval (11482451560 / 1000000000000) (11482533217 / 1000000000000)))) (orderedInterval (124144974 / 1000000000000) (124147209 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks0_1 :
    compactCertificate610.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4306666924664037 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2772518966 / 1000000000000) (2772518967 / 1000000000000), orderedInterval (-24159120222 / 1000000000000) (-24159120221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2486455308264573 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11383650035 / 1000000000000) (11383650036 / 1000000000000), orderedInterval (29899923385 / 1000000000000) (29899923386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4412258577637857 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21936849964 / 1000000000000) (-21936849847 / 1000000000000), orderedInterval (-9783518386 / 1000000000000) (-9783518269 / 1000000000000)))) (orderedInterval (-2767660923 / 1000000000000) (-2767660716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4122504306358533 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20486808176 / 1000000000000) (20486808181 / 1000000000000), orderedInterval (14061047048 / 1000000000000) (14061047052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2942013596160789 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26924810980 / 1000000000000) (26924810988 / 1000000000000), orderedInterval (11839645231 / 1000000000000) (11839645238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3335929855376931 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21572348550 / 1000000000000) (-21572342232 / 1000000000000), orderedInterval (17275114006 / 1000000000000) (17275120324 / 1000000000000)))) (orderedInterval (2285405631 / 1000000000000) (2285405722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2781150525242739 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29593976555 / 1000000000000) (-29593961024 / 1000000000000), orderedInterval (6331386339 / 1000000000000) (6331401870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2457230832885519 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19718519345 / 1000000000000) (-19718517729 / 1000000000000), orderedInterval (25462085100 / 1000000000000) (25462086716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (712201270542381 / 800000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24678842004 / 1000000000000) (-24678774781 / 1000000000000), orderedInterval (10312237411 / 1000000000000) (10312304634 / 1000000000000)))) (orderedInterval (154807910 / 1000000000000) (154809949 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks0_2 :
    compactCertificate610.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1969986195419607 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1856038462 / 1000000000000) (-1856038461 / 1000000000000), orderedInterval (-35903460989 / 1000000000000) (-35903460988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1669979114856927 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16916705771 / 1000000000000) (-16916705770 / 1000000000000), orderedInterval (-35174663136 / 1000000000000) (-35174663135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1044995390460981 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47313988814 / 1000000000000) (-47313988812 / 1000000000000), orderedInterval (-13988351984 / 1000000000000) (-13988351983 / 1000000000000)))) (orderedInterval (-286068464 / 1000000000000) (-286068343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (562001996487627 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (5826176093 / 1000000000000) (5826176111 / 1000000000000), orderedInterval (-67081671487 / 1000000000000) (-67081671469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1525944745423881 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34441890447 / 1000000000000) (-34441797730 / 1000000000000), orderedInterval (22012051087 / 1000000000000) (22012143803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2083547092847337 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5830169142 / 1000000000000) (5830169143 / 1000000000000), orderedInterval (34464596838 / 1000000000000) (34464596839 / 1000000000000)))) (orderedInterval (226977685 / 1000000000000) (226979846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (881004609539019 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48496607803 / 1000000000000) (48496607804 / 1000000000000), orderedInterval (23095528442 / 1000000000000) (23095528443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3581234825862699 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17981542106 / 1000000000000) (-17981542105 / 1000000000000), orderedInterval (-19680714626 / 1000000000000) (-19680714625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2392098894701541 / 4000000000000) 0 (IntervalRat.scale (963 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30797233453 / 1000000000000) (30797265461 / 1000000000000), orderedInterval (-10799188406 / 1000000000000) (-10799156398 / 1000000000000)))) (orderedInterval (-4022301087 / 1000000000000) (-4022294948 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks0 :
    compactCertificate610.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate610.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate610_chunkChecks0_0
    compactCertificate610_chunkChecks0_1 compactCertificate610_chunkChecks0_2

theorem compactCertificate610_chunkChecks1_0 :
    compactCertificate610.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (963 / 2) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36314839876 / 1000000000000) (-36314839001 / 1000000000000), orderedInterval (1879222751 / 1000000000000) (1879223626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1418682882828663 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18648985956 / 1000000000000) (-18648985955 / 1000000000000), orderedInterval (-38015482044 / 1000000000000) (-38015482043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (458772895627479 / 800000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20432266367 / 1000000000000) (20432268432 / 1000000000000), orderedInterval (-26336036908 / 1000000000000) (-26336034842 / 1000000000000)))) (orderedInterval (-1356670844 / 1000000000000) (-1356670315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (413968126963941 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44522013269 / 1000000000000) (-44522013268 / 1000000000000), orderedInterval (-64354288427 / 1000000000000) (-64354288426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3019232829374109 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29017971162 / 1000000000000) (29017974918 / 1000000000000), orderedInterval (-1192383660 / 1000000000000) (-1192379904 / 1000000000000)))) (orderedInterval (-404637639 / 1000000000000) (-404636178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2223953236918917 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22097467624 / 1000000000000) (-22097467623 / 1000000000000), orderedInterval (-25606786926 / 1000000000000) (-25606786925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3810781777529241 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25849452406 / 1000000000000) (-25849444813 / 1000000000000), orderedInterval (203326224 / 1000000000000) (203333817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2807004609539019 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27853134798 / 1000000000000) (-27853053141 / 1000000000000), orderedInterval (11482451560 / 1000000000000) (11482533217 / 1000000000000)))) (orderedInterval (392038911 / 1000000000000) (392042297 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks1_1 :
    compactCertificate610.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4306666924664037 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2772518966 / 1000000000000) (2772518967 / 1000000000000), orderedInterval (-24159120222 / 1000000000000) (-24159120221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2486455308264573 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11383650035 / 1000000000000) (11383650036 / 1000000000000), orderedInterval (29899923385 / 1000000000000) (29899923386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4412258577637857 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21936849964 / 1000000000000) (-21936849847 / 1000000000000), orderedInterval (-9783518386 / 1000000000000) (-9783518269 / 1000000000000)))) (orderedInterval (9272807824 / 1000000000000) (9272808258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4122504306358533 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20486808176 / 1000000000000) (20486808181 / 1000000000000), orderedInterval (14061047048 / 1000000000000) (14061047052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2942013596160789 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26924810980 / 1000000000000) (26924810988 / 1000000000000), orderedInterval (11839645231 / 1000000000000) (11839645238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3335929855376931 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21572348550 / 1000000000000) (-21572342232 / 1000000000000), orderedInterval (17275114006 / 1000000000000) (17275120324 / 1000000000000)))) (orderedInterval (1015440840 / 1000000000000) (1015440990 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2781150525242739 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29593976555 / 1000000000000) (-29593961024 / 1000000000000), orderedInterval (6331386339 / 1000000000000) (6331401870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2457230832885519 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19718519345 / 1000000000000) (-19718517729 / 1000000000000), orderedInterval (25462085100 / 1000000000000) (25462086716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (712201270542381 / 800000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24678842004 / 1000000000000) (-24678774781 / 1000000000000), orderedInterval (10312237411 / 1000000000000) (10312304634 / 1000000000000)))) (orderedInterval (-1265261062 / 1000000000000) (-1265257436 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks1_2 :
    compactCertificate610.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1969986195419607 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1856038462 / 1000000000000) (-1856038461 / 1000000000000), orderedInterval (-35903460989 / 1000000000000) (-35903460988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1669979114856927 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16916705771 / 1000000000000) (-16916705770 / 1000000000000), orderedInterval (-35174663136 / 1000000000000) (-35174663135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1044995390460981 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47313988814 / 1000000000000) (-47313988812 / 1000000000000), orderedInterval (-13988351984 / 1000000000000) (-13988351983 / 1000000000000)))) (orderedInterval (7350952278 / 1000000000000) (7350952390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (562001996487627 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (5826176093 / 1000000000000) (5826176111 / 1000000000000), orderedInterval (-67081671487 / 1000000000000) (-67081671469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1525944745423881 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34441890447 / 1000000000000) (-34441797730 / 1000000000000), orderedInterval (22012051087 / 1000000000000) (22012143803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2083547092847337 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5830169142 / 1000000000000) (5830169143 / 1000000000000), orderedInterval (34464596838 / 1000000000000) (34464596839 / 1000000000000)))) (orderedInterval (-2891605115 / 1000000000000) (-2891603396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (881004609539019 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48496607803 / 1000000000000) (48496607804 / 1000000000000), orderedInterval (23095528442 / 1000000000000) (23095528443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3581234825862699 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17981542106 / 1000000000000) (-17981542105 / 1000000000000), orderedInterval (-19680714626 / 1000000000000) (-19680714625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2392098894701541 / 4000000000000) 1 (IntervalRat.scale (963 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30797233453 / 1000000000000) (30797265461 / 1000000000000), orderedInterval (-10799188406 / 1000000000000) (-10799156398 / 1000000000000)))) (orderedInterval (5559112200 / 1000000000000) (5559119846 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks1 :
    compactCertificate610.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate610.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate610_chunkChecks1_0
    compactCertificate610_chunkChecks1_1 compactCertificate610_chunkChecks1_2

theorem compactCertificate610_chunkChecks2_0 :
    compactCertificate610.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (963 / 2) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36314839876 / 1000000000000) (-36314839001 / 1000000000000), orderedInterval (1879222751 / 1000000000000) (1879223626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1418682882828663 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18648985956 / 1000000000000) (-18648985955 / 1000000000000), orderedInterval (-38015482044 / 1000000000000) (-38015482043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (458772895627479 / 800000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20432266367 / 1000000000000) (20432268432 / 1000000000000), orderedInterval (-26336036908 / 1000000000000) (-26336034842 / 1000000000000)))) (orderedInterval (12790292072 / 1000000000000) (12790292635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (413968126963941 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44522013269 / 1000000000000) (-44522013268 / 1000000000000), orderedInterval (-64354288427 / 1000000000000) (-64354288426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3019232829374109 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29017971162 / 1000000000000) (29017974918 / 1000000000000), orderedInterval (-1192383660 / 1000000000000) (-1192379904 / 1000000000000)))) (orderedInterval (4621015613 / 1000000000000) (4621016927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2223953236918917 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22097467624 / 1000000000000) (-22097467623 / 1000000000000), orderedInterval (-25606786926 / 1000000000000) (-25606786925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3810781777529241 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25849452406 / 1000000000000) (-25849444813 / 1000000000000), orderedInterval (203326224 / 1000000000000) (203333817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2807004609539019 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27853134798 / 1000000000000) (-27853053141 / 1000000000000), orderedInterval (11482451560 / 1000000000000) (11482533217 / 1000000000000)))) (orderedInterval (-1692288797 / 1000000000000) (-1692283597 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks2_1 :
    compactCertificate610.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4306666924664037 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2772518966 / 1000000000000) (2772518967 / 1000000000000), orderedInterval (-24159120222 / 1000000000000) (-24159120221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2486455308264573 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11383650035 / 1000000000000) (11383650036 / 1000000000000), orderedInterval (29899923385 / 1000000000000) (29899923386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4412258577637857 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21936849964 / 1000000000000) (-21936849847 / 1000000000000), orderedInterval (-9783518386 / 1000000000000) (-9783518269 / 1000000000000)))) (orderedInterval (17404455840 / 1000000000000) (17404456775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4122504306358533 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20486808176 / 1000000000000) (20486808181 / 1000000000000), orderedInterval (14061047048 / 1000000000000) (14061047052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2942013596160789 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26924810980 / 1000000000000) (26924810988 / 1000000000000), orderedInterval (11839645231 / 1000000000000) (11839645238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3335929855376931 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21572348550 / 1000000000000) (-21572342232 / 1000000000000), orderedInterval (17275114006 / 1000000000000) (17275120324 / 1000000000000)))) (orderedInterval (-4576008867 / 1000000000000) (-4576008614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2781150525242739 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29593976555 / 1000000000000) (-29593961024 / 1000000000000), orderedInterval (6331386339 / 1000000000000) (6331401870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2457230832885519 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19718519345 / 1000000000000) (-19718517729 / 1000000000000), orderedInterval (25462085100 / 1000000000000) (25462086716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (712201270542381 / 800000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24678842004 / 1000000000000) (-24678774781 / 1000000000000), orderedInterval (10312237411 / 1000000000000) (10312304634 / 1000000000000)))) (orderedInterval (1038497586 / 1000000000000) (1038504101 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks2_2 :
    compactCertificate610.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1969986195419607 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1856038462 / 1000000000000) (-1856038461 / 1000000000000), orderedInterval (-35903460989 / 1000000000000) (-35903460988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1669979114856927 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16916705771 / 1000000000000) (-16916705770 / 1000000000000), orderedInterval (-35174663136 / 1000000000000) (-35174663135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1044995390460981 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47313988814 / 1000000000000) (-47313988812 / 1000000000000), orderedInterval (-13988351984 / 1000000000000) (-13988351983 / 1000000000000)))) (orderedInterval (-592144754 / 1000000000000) (-592144647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (562001996487627 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (5826176093 / 1000000000000) (5826176111 / 1000000000000), orderedInterval (-67081671487 / 1000000000000) (-67081671469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1525944745423881 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34441890447 / 1000000000000) (-34441797730 / 1000000000000), orderedInterval (22012051087 / 1000000000000) (22012143803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2083547092847337 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5830169142 / 1000000000000) (5830169143 / 1000000000000), orderedInterval (34464596838 / 1000000000000) (34464596839 / 1000000000000)))) (orderedInterval (47586467 / 1000000000000) (47587843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (881004609539019 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48496607803 / 1000000000000) (48496607804 / 1000000000000), orderedInterval (23095528442 / 1000000000000) (23095528443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3581234825862699 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17981542106 / 1000000000000) (-17981542105 / 1000000000000), orderedInterval (-19680714626 / 1000000000000) (-19680714625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2392098894701541 / 4000000000000) 2 (IntervalRat.scale (963 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30797233453 / 1000000000000) (30797265461 / 1000000000000), orderedInterval (-10799188406 / 1000000000000) (-10799156398 / 1000000000000)))) (orderedInterval (3780113741 / 1000000000000) (3780123297 / 1000000000000))) = true
  rfl'

theorem compactCertificate610_chunkChecks2 :
    compactCertificate610.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate610.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate610_chunkChecks2_0
    compactCertificate610_chunkChecks2_1 compactCertificate610_chunkChecks2_2

theorem compactCertificate610_chunkChecks3_0 :
    compactCertificate610.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (963 / 2) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36314839876 / 1000000000000) (-36314839001 / 1000000000000), orderedInterval (1879222751 / 1000000000000) (1879223626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1418682882828663 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18648985956 / 1000000000000) (-18648985955 / 1000000000000), orderedInterval (-38015482044 / 1000000000000) (-38015482043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (458772895627479 / 800000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20432266367 / 1000000000000) (20432268432 / 1000000000000), orderedInterval (-26336036908 / 1000000000000) (-26336034842 / 1000000000000)))) (orderedInterval (1981001446 / 1000000000000) (1981002050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (413968126963941 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44522013269 / 1000000000000) (-44522013268 / 1000000000000), orderedInterval (-64354288427 / 1000000000000) (-64354288426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3019232829374109 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29017971162 / 1000000000000) (29017974918 / 1000000000000), orderedInterval (-1192383660 / 1000000000000) (-1192379904 / 1000000000000)))) (orderedInterval (-113881768 / 1000000000000) (-113880275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2223953236918917 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22097467624 / 1000000000000) (-22097467623 / 1000000000000), orderedInterval (-25606786926 / 1000000000000) (-25606786925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3810781777529241 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25849452406 / 1000000000000) (-25849444813 / 1000000000000), orderedInterval (203326224 / 1000000000000) (203333817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2807004609539019 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27853134798 / 1000000000000) (-27853053141 / 1000000000000), orderedInterval (11482451560 / 1000000000000) (11482533217 / 1000000000000)))) (orderedInterval (-806997546 / 1000000000000) (-806989459 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate610_chunkChecks3_1 :
    compactCertificate610.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4306666924664037 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2772518966 / 1000000000000) (2772518967 / 1000000000000), orderedInterval (-24159120222 / 1000000000000) (-24159120221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2486455308264573 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11383650035 / 1000000000000) (11383650036 / 1000000000000), orderedInterval (29899923385 / 1000000000000) (29899923386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4412258577637857 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21936849964 / 1000000000000) (-21936849847 / 1000000000000), orderedInterval (-9783518386 / 1000000000000) (-9783518269 / 1000000000000)))) (orderedInterval (-36076089694 / 1000000000000) (-36076087634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4122504306358533 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20486808176 / 1000000000000) (20486808181 / 1000000000000), orderedInterval (14061047048 / 1000000000000) (14061047052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2942013596160789 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26924810980 / 1000000000000) (26924810988 / 1000000000000), orderedInterval (11839645231 / 1000000000000) (11839645238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3335929855376931 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21572348550 / 1000000000000) (-21572342232 / 1000000000000), orderedInterval (17275114006 / 1000000000000) (17275120324 / 1000000000000)))) (orderedInterval (-1037371431 / 1000000000000) (-1037371001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2781150525242739 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29593976555 / 1000000000000) (-29593961024 / 1000000000000), orderedInterval (6331386339 / 1000000000000) (6331401870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2457230832885519 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19718519345 / 1000000000000) (-19718517729 / 1000000000000), orderedInterval (25462085100 / 1000000000000) (25462086716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (712201270542381 / 800000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24678842004 / 1000000000000) (-24678774781 / 1000000000000), orderedInterval (10312237411 / 1000000000000) (10312304634 / 1000000000000)))) (orderedInterval (1134816056 / 1000000000000) (1134827833 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate610_chunkChecks3_2 :
    compactCertificate610.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1969986195419607 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1856038462 / 1000000000000) (-1856038461 / 1000000000000), orderedInterval (-35903460989 / 1000000000000) (-35903460988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1669979114856927 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16916705771 / 1000000000000) (-16916705770 / 1000000000000), orderedInterval (-35174663136 / 1000000000000) (-35174663135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1044995390460981 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47313988814 / 1000000000000) (-47313988812 / 1000000000000), orderedInterval (-13988351984 / 1000000000000) (-13988351983 / 1000000000000)))) (orderedInterval (-7366870759 / 1000000000000) (-7366870656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (562001996487627 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (5826176093 / 1000000000000) (5826176111 / 1000000000000), orderedInterval (-67081671487 / 1000000000000) (-67081671469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1525944745423881 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34441890447 / 1000000000000) (-34441797730 / 1000000000000), orderedInterval (22012051087 / 1000000000000) (22012143803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2083547092847337 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5830169142 / 1000000000000) (5830169143 / 1000000000000), orderedInterval (34464596838 / 1000000000000) (34464596839 / 1000000000000)))) (orderedInterval (3561451965 / 1000000000000) (3561453067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (881004609539019 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48496607803 / 1000000000000) (48496607804 / 1000000000000), orderedInterval (23095528442 / 1000000000000) (23095528443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3581234825862699 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17981542106 / 1000000000000) (-17981542105 / 1000000000000), orderedInterval (-19680714626 / 1000000000000) (-19680714625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2392098894701541 / 4000000000000) 3 (IntervalRat.scale (963 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30797233453 / 1000000000000) (30797265461 / 1000000000000), orderedInterval (-10799188406 / 1000000000000) (-10799156398 / 1000000000000)))) (orderedInterval (-14202357236 / 1000000000000) (-14202345284 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate610_chunkChecks3 :
    compactCertificate610.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate610.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate610_chunkChecks3_0
    compactCertificate610_chunkChecks3_1 compactCertificate610_chunkChecks3_2

theorem compactCertificate610_chunkChecks4_0 :
    compactCertificate610.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (963 / 2) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36314839876 / 1000000000000) (-36314839001 / 1000000000000), orderedInterval (1879222751 / 1000000000000) (1879223626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1418682882828663 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-18648985956 / 1000000000000) (-18648985955 / 1000000000000), orderedInterval (-38015482044 / 1000000000000) (-38015482043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (458772895627479 / 800000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20432266367 / 1000000000000) (20432268432 / 1000000000000), orderedInterval (-26336036908 / 1000000000000) (-26336034842 / 1000000000000)))) (orderedInterval (-12040795847 / 1000000000000) (-12040795195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (413968126963941 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44522013269 / 1000000000000) (-44522013268 / 1000000000000), orderedInterval (-64354288427 / 1000000000000) (-64354288426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3019232829374109 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29017971162 / 1000000000000) (29017974918 / 1000000000000), orderedInterval (-1192383660 / 1000000000000) (-1192379904 / 1000000000000)))) (orderedInterval (-12313792570 / 1000000000000) (-12313790554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2223953236918917 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22097467624 / 1000000000000) (-22097467623 / 1000000000000), orderedInterval (-25606786926 / 1000000000000) (-25606786925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3810781777529241 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25849452406 / 1000000000000) (-25849444813 / 1000000000000), orderedInterval (203326224 / 1000000000000) (203333817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2807004609539019 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-27853134798 / 1000000000000) (-27853053141 / 1000000000000), orderedInterval (11482451560 / 1000000000000) (11482533217 / 1000000000000)))) (orderedInterval (9185710672 / 1000000000000) (9185723479 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate610_chunkChecks4_1 :
    compactCertificate610.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4306666924664037 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2772518966 / 1000000000000) (2772518967 / 1000000000000), orderedInterval (-24159120222 / 1000000000000) (-24159120221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2486455308264573 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11383650035 / 1000000000000) (11383650036 / 1000000000000), orderedInterval (29899923385 / 1000000000000) (29899923386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4412258577637857 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21936849964 / 1000000000000) (-21936849847 / 1000000000000), orderedInterval (-9783518386 / 1000000000000) (-9783518269 / 1000000000000)))) (orderedInterval (-95716292640 / 1000000000000) (-95716288051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4122504306358533 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20486808176 / 1000000000000) (20486808181 / 1000000000000), orderedInterval (14061047048 / 1000000000000) (14061047052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2942013596160789 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26924810980 / 1000000000000) (26924810988 / 1000000000000), orderedInterval (11839645231 / 1000000000000) (11839645238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3335929855376931 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21572348550 / 1000000000000) (-21572342232 / 1000000000000), orderedInterval (17275114006 / 1000000000000) (17275120324 / 1000000000000)))) (orderedInterval (7085558866 / 1000000000000) (7085559614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2781150525242739 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29593976555 / 1000000000000) (-29593961024 / 1000000000000), orderedInterval (6331386339 / 1000000000000) (6331401870 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2457230832885519 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19718519345 / 1000000000000) (-19718517729 / 1000000000000), orderedInterval (25462085100 / 1000000000000) (25462086716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (712201270542381 / 800000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24678842004 / 1000000000000) (-24678774781 / 1000000000000), orderedInterval (10312237411 / 1000000000000) (10312304634 / 1000000000000)))) (orderedInterval (-5884918212 / 1000000000000) (-5884896784 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate610_chunkChecks4_2 :
    compactCertificate610.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1969986195419607 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1856038462 / 1000000000000) (-1856038461 / 1000000000000), orderedInterval (-35903460989 / 1000000000000) (-35903460988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1669979114856927 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-16916705771 / 1000000000000) (-16916705770 / 1000000000000), orderedInterval (-35174663136 / 1000000000000) (-35174663135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1044995390460981 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47313988814 / 1000000000000) (-47313988812 / 1000000000000), orderedInterval (-13988351984 / 1000000000000) (-13988351983 / 1000000000000)))) (orderedInterval (763119934 / 1000000000000) (763120036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (562001996487627 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (5826176093 / 1000000000000) (5826176111 / 1000000000000), orderedInterval (-67081671487 / 1000000000000) (-67081671469 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1525944745423881 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-34441890447 / 1000000000000) (-34441797730 / 1000000000000), orderedInterval (22012051087 / 1000000000000) (22012143803 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2083547092847337 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5830169142 / 1000000000000) (5830169143 / 1000000000000), orderedInterval (34464596838 / 1000000000000) (34464596839 / 1000000000000)))) (orderedInterval (-319640080 / 1000000000000) (-319639191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (881004609539019 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (48496607803 / 1000000000000) (48496607804 / 1000000000000), orderedInterval (23095528442 / 1000000000000) (23095528443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3581234825862699 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17981542106 / 1000000000000) (-17981542105 / 1000000000000), orderedInterval (-19680714626 / 1000000000000) (-19680714625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2392098894701541 / 4000000000000) 4 (IntervalRat.scale (963 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30797233453 / 1000000000000) (30797265461 / 1000000000000), orderedInterval (-10799188406 / 1000000000000) (-10799156398 / 1000000000000)))) (orderedInterval (3819095777 / 1000000000000) (3819110801 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate610_chunkChecks4 :
    compactCertificate610.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate610.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate610_chunkChecks4_0
    compactCertificate610_chunkChecks4_1 compactCertificate610_chunkChecks4_2

theorem compactCertificate610_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate610.chunkCheck r b = true :=
  compactCertificate610.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate610_chunkChecks0
    · exact compactCertificate610_chunkChecks1
    · exact compactCertificate610_chunkChecks2
    · exact compactCertificate610_chunkChecks3
    · exact compactCertificate610_chunkChecks4)

theorem compactCertificate610_coefficient0 :
    compactCertificate610.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate610_coefficient1 :
    compactCertificate610.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate610_coefficient2 :
    compactCertificate610.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate610_coefficient3 :
    compactCertificate610.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate610_coefficient4 :
    compactCertificate610.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate610_coefficients : ∀ r : Fin 5,
    compactCertificate610.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate610_coefficient0
  · exact compactCertificate610_coefficient1
  · exact compactCertificate610_coefficient2
  · exact compactCertificate610_coefficient3
  · exact compactCertificate610_coefficient4

theorem compactCertificate610_lower : (1 : ℚ) ≤ compactCertificate610.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate610, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate610_proves {t : ℝ} (ht : t ∈ compactCertificate610.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate610.proves compactCertificate610_states compactCertificate610_chunks
    compactCertificate610_coefficients compactCertificate610_lower ht

end Erdos232
