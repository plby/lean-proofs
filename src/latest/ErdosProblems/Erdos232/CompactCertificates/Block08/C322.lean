/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate322 : CompactCertificate where
  left := 194
  right := 195
  center := 389 / 2
  grid := fun i =>
    match i.val with
    | 0 => 62
    | 1 => 46
    | 2 => 74
    | 3 => 13
    | 4 => 36
    | 5 => 97
    | 6 => 72
    | 7 => 123
    | 8 => 90
    | 9 => 139
    | 10 => 80
    | 11 => 142
    | 12 => 133
    | 13 => 95
    | 14 => 107
    | 15 => 89
    | 16 => 79
    | 17 => 115
    | 18 => 63
    | 19 => 54
    | 20 => 34
    | 21 => 18
    | 22 => 49
    | 23 => 67
    | 24 => 28
    | 25 => 115
    | _ => 77
  point := fun i =>
    match i.val with
    | 0 => 389 / 2
    | 1 => 573071278733489 / 4000000000000
    | 2 => 185319477049937 / 800000000000
    | 3 => 167220769874323 / 4000000000000
    | 4 => 449178509429431 / 4000000000000
    | 5 => 1219607030764827 / 4000000000000
    | 6 => 898357018859251 / 4000000000000
    | 7 => 1539350063820223 / 4000000000000
    | 8 => 1133878289834557 / 4000000000000
    | 9 => 1739660886494611 / 4000000000000
    | 10 => 1004393681116219 / 4000000000000
    | 11 => 1782314212566071 / 4000000000000
    | 12 => 1665269133098099 / 4000000000000
    | 13 => 1188414630224867 / 4000000000000
    | 14 => 1347535528288293 / 4000000000000
    | 15 => 1123434635845717 / 4000000000000
    | 16 => 992588571124057 / 4000000000000
    | 17 => 287690855909643 / 800000000000
    | 18 => 795768047786321 / 4000000000000
    | 19 => 674581386998281 / 4000000000000
    | 20 => 422121710165443 / 4000000000000
    | 21 => 227018459640381 / 4000000000000
    | 22 => 616399279304143 / 4000000000000
    | 23 => 841640518294511 / 4000000000000
    | 24 => 355878289834557 / 4000000000000
    | 25 => 1446625490405597 / 4000000000000
    | _ => 966278785087123 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (27729712636 / 1000000000000) (27729712637 / 1000000000000), orderedInterval (49970479820 / 1000000000000) (49970479821 / 1000000000000))
    | 1 => (orderedInterval (-29648262969 / 1000000000000) (-29648260435 / 1000000000000), orderedInterval (59807415586 / 1000000000000) (59807418120 / 1000000000000))
    | 2 => (orderedInterval (-2287626884 / 1000000000000) (-2287626879 / 1000000000000), orderedInterval (52378381558 / 1000000000000) (52378381563 / 1000000000000))
    | 3 => (orderedInterval (-121489931732 / 1000000000000) (-121489931467 / 1000000000000), orderedInterval (23072775957 / 1000000000000) (23072776223 / 1000000000000))
    | 4 => (orderedInterval (-1387064631 / 1000000000000) (-1387064623 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
    | 5 => (orderedInterval (-37228196465 / 1000000000000) (-37228196464 / 1000000000000), orderedInterval (-26434439944 / 1000000000000) (-26434439943 / 1000000000000))
    | 6 => (orderedInterval (-38947727560 / 1000000000000) (-38947669883 / 1000000000000), orderedInterval (36386431168 / 1000000000000) (36386488845 / 1000000000000))
    | 7 => (orderedInterval (28986367124 / 1000000000000) (28986388769 / 1000000000000), orderedInterval (-28569159937 / 1000000000000) (-28569138292 / 1000000000000))
    | 8 => (orderedInterval (47305818154 / 1000000000000) (47305818207 / 1000000000000), orderedInterval (2739594363 / 1000000000000) (2739594416 / 1000000000000))
    | 9 => (orderedInterval (31796528489 / 1000000000000) (31796620114 / 1000000000000), orderedInterval (-21314673218 / 1000000000000) (-21314581593 / 1000000000000))
    | 10 => (orderedInterval (26571566049 / 1000000000000) (26571566050 / 1000000000000), orderedInterval (42717332946 / 1000000000000) (42717332947 / 1000000000000))
    | 11 => (orderedInterval (9626490440 / 1000000000000) (9626490441 / 1000000000000), orderedInterval (36541627938 / 1000000000000) (36541627939 / 1000000000000))
    | 12 => (orderedInterval (26061383747 / 1000000000000) (26061393744 / 1000000000000), orderedInterval (-29185615332 / 1000000000000) (-29185605335 / 1000000000000))
    | 13 => (orderedInterval (24693040800 / 1000000000000) (24693044103 / 1000000000000), orderedInterval (-39195204113 / 1000000000000) (-39195200809 / 1000000000000))
    | 14 => (orderedInterval (-43411565765 / 1000000000000) (-43411565678 / 1000000000000), orderedInterval (-2208115524 / 1000000000000) (-2208115437 / 1000000000000))
    | 15 => (orderedInterval (-42424260344 / 1000000000000) (-42424235166 / 1000000000000), orderedInterval (21682733161 / 1000000000000) (21682758339 / 1000000000000))
    | 16 => (orderedInterval (-34385017933 / 1000000000000) (-34385017932 / 1000000000000), orderedInterval (-37121629736 / 1000000000000) (-37121629735 / 1000000000000))
    | 17 => (orderedInterval (32549869686 / 1000000000000) (32549925230 / 1000000000000), orderedInterval (-26705971929 / 1000000000000) (-26705916385 / 1000000000000))
    | 18 => (orderedInterval (-55005312528 / 1000000000000) (-55005311092 / 1000000000000), orderedInterval (13345569628 / 1000000000000) (13345571064 / 1000000000000))
    | 19 => (orderedInterval (-13168080762 / 1000000000000) (-13168080660 / 1000000000000), orderedInterval (60051700697 / 1000000000000) (60051700799 / 1000000000000))
    | 20 => (orderedInterval (-37203120738 / 1000000000000) (-37203116022 / 1000000000000), orderedInterval (68356429324 / 1000000000000) (68356434041 / 1000000000000))
    | 21 => (orderedInterval (88492482572 / 1000000000000) (88492482573 / 1000000000000), orderedInterval (57409504037 / 1000000000000) (57409504038 / 1000000000000))
    | 22 => (orderedInterval (-52145592420 / 1000000000000) (-52145592419 / 1000000000000), orderedInterval (-37408023573 / 1000000000000) (-37408023572 / 1000000000000))
    | 23 => (orderedInterval (-35780380951 / 1000000000000) (-35780380950 / 1000000000000), orderedInterval (-41692712768 / 1000000000000) (-41692712767 / 1000000000000))
    | 24 => (orderedInterval (82584117158 / 1000000000000) (82584117761 / 1000000000000), orderedInterval (-18773623127 / 1000000000000) (-18773622523 / 1000000000000))
    | 25 => (orderedInterval (-38436145470 / 1000000000000) (-38436145468 / 1000000000000), orderedInterval (-16767999097 / 1000000000000) (-16767999096 / 1000000000000))
    | _ => (orderedInterval (-22418960056 / 1000000000000) (-22418960055 / 1000000000000), orderedInterval (-46135194352 / 1000000000000) (-46135194351 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10580582501 / 1000000000000) (10580582540 / 1000000000000)
      | 1 => orderedInterval (3913974578 / 1000000000000) (3913974606 / 1000000000000)
      | 2 => orderedInterval (249232080 / 1000000000000) (249232761 / 1000000000000)
      | 3 => orderedInterval (-2312678799 / 1000000000000) (-2312662440 / 1000000000000)
      | 4 => orderedInterval (2084243641 / 1000000000000) (2084244158 / 1000000000000)
      | 5 => orderedInterval (2311244183 / 1000000000000) (2311245915 / 1000000000000)
      | 6 => orderedInterval (8329088597 / 1000000000000) (8329089035 / 1000000000000)
      | 7 => orderedInterval (2291163767 / 1000000000000) (2291163791 / 1000000000000)
      | _ => orderedInterval (7833006275 / 1000000000000) (7833006333 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (23877728228 / 1000000000000) (23877728262 / 1000000000000)
      | 1 => orderedInterval (4479159852 / 1000000000000) (4479159880 / 1000000000000)
      | 2 => orderedInterval (1840011934 / 1000000000000) (1840013277 / 1000000000000)
      | 3 => orderedInterval (24455046050 / 1000000000000) (24455082615 / 1000000000000)
      | 4 => orderedInterval (-4514500004 / 1000000000000) (-4514499101 / 1000000000000)
      | 5 => orderedInterval (1807596870 / 1000000000000) (1807599947 / 1000000000000)
      | 6 => orderedInterval (-3922276817 / 1000000000000) (-3922276448 / 1000000000000)
      | 7 => orderedInterval (3819720981 / 1000000000000) (3819721002 / 1000000000000)
      | _ => orderedInterval (13237245819 / 1000000000000) (13237245897 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-10773541109 / 1000000000000) (-10773541077 / 1000000000000)
      | 1 => orderedInterval (-6570717086 / 1000000000000) (-6570717048 / 1000000000000)
      | 2 => orderedInterval (1062185304 / 1000000000000) (1062187961 / 1000000000000)
      | 3 => orderedInterval (17660391794 / 1000000000000) (17660473728 / 1000000000000)
      | 4 => orderedInterval (-3928737765 / 1000000000000) (-3928736141 / 1000000000000)
      | 5 => orderedInterval (-5039689366 / 1000000000000) (-5039683842 / 1000000000000)
      | 6 => orderedInterval (-9384862774 / 1000000000000) (-9384862439 / 1000000000000)
      | 7 => orderedInterval (-3832248130 / 1000000000000) (-3832248108 / 1000000000000)
      | _ => orderedInterval (-17478388331 / 1000000000000) (-17478388217 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-25165853118 / 1000000000000) (-25165853087 / 1000000000000)
      | 1 => orderedInterval (-7731951186 / 1000000000000) (-7731951130 / 1000000000000)
      | 2 => orderedInterval (-7035992997 / 1000000000000) (-7035987747 / 1000000000000)
      | 3 => orderedInterval (-111699065278 / 1000000000000) (-111698882085 / 1000000000000)
      | 4 => orderedInterval (8005542695 / 1000000000000) (8005545695 / 1000000000000)
      | 5 => orderedInterval (-817733303 / 1000000000000) (-817723348 / 1000000000000)
      | 6 => orderedInterval (4191793201 / 1000000000000) (4191793519 / 1000000000000)
      | 7 => orderedInterval (-4421226839 / 1000000000000) (-4421226817 / 1000000000000)
      | _ => orderedInterval (-25258128787 / 1000000000000) (-25258128613 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10898142855 / 1000000000000) (10898142887 / 1000000000000)
      | 1 => orderedInterval (16058829658 / 1000000000000) (16058829744 / 1000000000000)
      | 2 => orderedInterval (-8471744008 / 1000000000000) (-8471733603 / 1000000000000)
      | 3 => orderedInterval (-96936938342 / 1000000000000) (-96936527789 / 1000000000000)
      | 4 => orderedInterval (4732074071 / 1000000000000) (4732079777 / 1000000000000)
      | 5 => orderedInterval (12830904017 / 1000000000000) (12830922099 / 1000000000000)
      | 6 => orderedInterval (9899271125 / 1000000000000) (9899271437 / 1000000000000)
      | 7 => orderedInterval (4255285349 / 1000000000000) (4255285372 / 1000000000000)
      | _ => orderedInterval (47690999928 / 1000000000000) (47691000208 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (35279856823 / 1000000000000) (35279876699 / 1000000000000)
    | 1 => orderedInterval (65079732913 / 1000000000000) (65079775331 / 1000000000000)
    | 2 => orderedInterval (-38285607463 / 1000000000000) (-38285515183 / 1000000000000)
    | 3 => orderedInterval (-169932615612 / 1000000000000) (-169932413613 / 1000000000000)
    | _ => orderedInterval (956824653 / 1000000000000) (957270132 / 1000000000000)

theorem compactCertificate322_stateChecks0 :
    compactCertificate322.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (389 / 2)) (orderedInterval (27729712636 / 1000000000000) (27729712637 / 1000000000000), orderedInterval (49970479820 / 1000000000000) (49970479821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (573071278733489 / 4000000000000)) (orderedInterval (-29648262969 / 1000000000000) (-29648260435 / 1000000000000), orderedInterval (59807415586 / 1000000000000) (59807418120 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (185319477049937 / 800000000000)) (orderedInterval (-2287626884 / 1000000000000) (-2287626879 / 1000000000000), orderedInterval (52378381558 / 1000000000000) (52378381563 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks1 :
    compactCertificate322.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (167220769874323 / 4000000000000)) (orderedInterval (-121489931732 / 1000000000000) (-121489931467 / 1000000000000), orderedInterval (23072775957 / 1000000000000) (23072776223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (449178509429431 / 4000000000000)) (orderedInterval (-1387064631 / 1000000000000) (-1387064623 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1219607030764827 / 4000000000000)) (orderedInterval (-37228196465 / 1000000000000) (-37228196464 / 1000000000000), orderedInterval (-26434439944 / 1000000000000) (-26434439943 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks2 :
    compactCertificate322.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (898357018859251 / 4000000000000)) (orderedInterval (-38947727560 / 1000000000000) (-38947669883 / 1000000000000), orderedInterval (36386431168 / 1000000000000) (36386488845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1539350063820223 / 4000000000000)) (orderedInterval (28986367124 / 1000000000000) (28986388769 / 1000000000000), orderedInterval (-28569159937 / 1000000000000) (-28569138292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1133878289834557 / 4000000000000)) (orderedInterval (47305818154 / 1000000000000) (47305818207 / 1000000000000), orderedInterval (2739594363 / 1000000000000) (2739594416 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks3 :
    compactCertificate322.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1739660886494611 / 4000000000000)) (orderedInterval (31796528489 / 1000000000000) (31796620114 / 1000000000000), orderedInterval (-21314673218 / 1000000000000) (-21314581593 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1004393681116219 / 4000000000000)) (orderedInterval (26571566049 / 1000000000000) (26571566050 / 1000000000000), orderedInterval (42717332946 / 1000000000000) (42717332947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1782314212566071 / 4000000000000)) (orderedInterval (9626490440 / 1000000000000) (9626490441 / 1000000000000), orderedInterval (36541627938 / 1000000000000) (36541627939 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks4 :
    compactCertificate322.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1665269133098099 / 4000000000000)) (orderedInterval (26061383747 / 1000000000000) (26061393744 / 1000000000000), orderedInterval (-29185615332 / 1000000000000) (-29185605335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1188414630224867 / 4000000000000)) (orderedInterval (24693040800 / 1000000000000) (24693044103 / 1000000000000), orderedInterval (-39195204113 / 1000000000000) (-39195200809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1347535528288293 / 4000000000000)) (orderedInterval (-43411565765 / 1000000000000) (-43411565678 / 1000000000000), orderedInterval (-2208115524 / 1000000000000) (-2208115437 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks5 :
    compactCertificate322.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1123434635845717 / 4000000000000)) (orderedInterval (-42424260344 / 1000000000000) (-42424235166 / 1000000000000), orderedInterval (21682733161 / 1000000000000) (21682758339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (992588571124057 / 4000000000000)) (orderedInterval (-34385017933 / 1000000000000) (-34385017932 / 1000000000000), orderedInterval (-37121629736 / 1000000000000) (-37121629735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (287690855909643 / 800000000000)) (orderedInterval (32549869686 / 1000000000000) (32549925230 / 1000000000000), orderedInterval (-26705971929 / 1000000000000) (-26705916385 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks6 :
    compactCertificate322.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (795768047786321 / 4000000000000)) (orderedInterval (-55005312528 / 1000000000000) (-55005311092 / 1000000000000), orderedInterval (13345569628 / 1000000000000) (13345571064 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (674581386998281 / 4000000000000)) (orderedInterval (-13168080762 / 1000000000000) (-13168080660 / 1000000000000), orderedInterval (60051700697 / 1000000000000) (60051700799 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (422121710165443 / 4000000000000)) (orderedInterval (-37203120738 / 1000000000000) (-37203116022 / 1000000000000), orderedInterval (68356429324 / 1000000000000) (68356434041 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks7 :
    compactCertificate322.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (227018459640381 / 4000000000000)) (orderedInterval (88492482572 / 1000000000000) (88492482573 / 1000000000000), orderedInterval (57409504037 / 1000000000000) (57409504038 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (616399279304143 / 4000000000000)) (orderedInterval (-52145592420 / 1000000000000) (-52145592419 / 1000000000000), orderedInterval (-37408023573 / 1000000000000) (-37408023572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (841640518294511 / 4000000000000)) (orderedInterval (-35780380951 / 1000000000000) (-35780380950 / 1000000000000), orderedInterval (-41692712768 / 1000000000000) (-41692712767 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_stateChecks8 :
    compactCertificate322.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (355878289834557 / 4000000000000)) (orderedInterval (82584117158 / 1000000000000) (82584117761 / 1000000000000), orderedInterval (-18773623127 / 1000000000000) (-18773622523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1446625490405597 / 4000000000000)) (orderedInterval (-38436145470 / 1000000000000) (-38436145468 / 1000000000000), orderedInterval (-16767999097 / 1000000000000) (-16767999096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (966278785087123 / 4000000000000)) (orderedInterval (-22418960056 / 1000000000000) (-22418960055 / 1000000000000), orderedInterval (-46135194352 / 1000000000000) (-46135194351 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_states : ∀ j,
    BesselStateValid (compactCertificate322.point j) (compactCertificate322.state j) :=
  compactCertificate322.statesValid_of_checks3 compactCertificate322_stateChecks0
    compactCertificate322_stateChecks1 compactCertificate322_stateChecks2
    compactCertificate322_stateChecks3 compactCertificate322_stateChecks4
    compactCertificate322_stateChecks5 compactCertificate322_stateChecks6
    compactCertificate322_stateChecks7 compactCertificate322_stateChecks8

theorem compactCertificate322_chunkChecks0_0 :
    compactCertificate322.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (389 / 2) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27729712636 / 1000000000000) (27729712637 / 1000000000000), orderedInterval (49970479820 / 1000000000000) (49970479821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (573071278733489 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29648262969 / 1000000000000) (-29648260435 / 1000000000000), orderedInterval (59807415586 / 1000000000000) (59807418120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (185319477049937 / 800000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2287626884 / 1000000000000) (-2287626879 / 1000000000000), orderedInterval (52378381558 / 1000000000000) (52378381563 / 1000000000000)))) (orderedInterval (10580582501 / 1000000000000) (10580582540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (167220769874323 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-121489931732 / 1000000000000) (-121489931467 / 1000000000000), orderedInterval (23072775957 / 1000000000000) (23072776223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (449178509429431 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1387064631 / 1000000000000) (-1387064623 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1219607030764827 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37228196465 / 1000000000000) (-37228196464 / 1000000000000), orderedInterval (-26434439944 / 1000000000000) (-26434439943 / 1000000000000)))) (orderedInterval (3913974578 / 1000000000000) (3913974606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (898357018859251 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38947727560 / 1000000000000) (-38947669883 / 1000000000000), orderedInterval (36386431168 / 1000000000000) (36386488845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1539350063820223 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28986367124 / 1000000000000) (28986388769 / 1000000000000), orderedInterval (-28569159937 / 1000000000000) (-28569138292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1133878289834557 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47305818154 / 1000000000000) (47305818207 / 1000000000000), orderedInterval (2739594363 / 1000000000000) (2739594416 / 1000000000000)))) (orderedInterval (249232080 / 1000000000000) (249232761 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks0_1 :
    compactCertificate322.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1739660886494611 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31796528489 / 1000000000000) (31796620114 / 1000000000000), orderedInterval (-21314673218 / 1000000000000) (-21314581593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1004393681116219 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26571566049 / 1000000000000) (26571566050 / 1000000000000), orderedInterval (42717332946 / 1000000000000) (42717332947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1782314212566071 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9626490440 / 1000000000000) (9626490441 / 1000000000000), orderedInterval (36541627938 / 1000000000000) (36541627939 / 1000000000000)))) (orderedInterval (-2312678799 / 1000000000000) (-2312662440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1665269133098099 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26061383747 / 1000000000000) (26061393744 / 1000000000000), orderedInterval (-29185615332 / 1000000000000) (-29185605335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1188414630224867 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24693040800 / 1000000000000) (24693044103 / 1000000000000), orderedInterval (-39195204113 / 1000000000000) (-39195200809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1347535528288293 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43411565765 / 1000000000000) (-43411565678 / 1000000000000), orderedInterval (-2208115524 / 1000000000000) (-2208115437 / 1000000000000)))) (orderedInterval (2084243641 / 1000000000000) (2084244158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1123434635845717 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42424260344 / 1000000000000) (-42424235166 / 1000000000000), orderedInterval (21682733161 / 1000000000000) (21682758339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (992588571124057 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34385017933 / 1000000000000) (-34385017932 / 1000000000000), orderedInterval (-37121629736 / 1000000000000) (-37121629735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (287690855909643 / 800000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32549869686 / 1000000000000) (32549925230 / 1000000000000), orderedInterval (-26705971929 / 1000000000000) (-26705916385 / 1000000000000)))) (orderedInterval (2311244183 / 1000000000000) (2311245915 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks0_2 :
    compactCertificate322.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (795768047786321 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55005312528 / 1000000000000) (-55005311092 / 1000000000000), orderedInterval (13345569628 / 1000000000000) (13345571064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (674581386998281 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13168080762 / 1000000000000) (-13168080660 / 1000000000000), orderedInterval (60051700697 / 1000000000000) (60051700799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (422121710165443 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37203120738 / 1000000000000) (-37203116022 / 1000000000000), orderedInterval (68356429324 / 1000000000000) (68356434041 / 1000000000000)))) (orderedInterval (8329088597 / 1000000000000) (8329089035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (227018459640381 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88492482572 / 1000000000000) (88492482573 / 1000000000000), orderedInterval (57409504037 / 1000000000000) (57409504038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (616399279304143 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52145592420 / 1000000000000) (-52145592419 / 1000000000000), orderedInterval (-37408023573 / 1000000000000) (-37408023572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (841640518294511 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35780380951 / 1000000000000) (-35780380950 / 1000000000000), orderedInterval (-41692712768 / 1000000000000) (-41692712767 / 1000000000000)))) (orderedInterval (2291163767 / 1000000000000) (2291163791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (355878289834557 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82584117158 / 1000000000000) (82584117761 / 1000000000000), orderedInterval (-18773623127 / 1000000000000) (-18773622523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1446625490405597 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38436145470 / 1000000000000) (-38436145468 / 1000000000000), orderedInterval (-16767999097 / 1000000000000) (-16767999096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (966278785087123 / 4000000000000) 0 (IntervalRat.scale (389 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22418960056 / 1000000000000) (-22418960055 / 1000000000000), orderedInterval (-46135194352 / 1000000000000) (-46135194351 / 1000000000000)))) (orderedInterval (7833006275 / 1000000000000) (7833006333 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks0 :
    compactCertificate322.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate322.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate322_chunkChecks0_0
    compactCertificate322_chunkChecks0_1 compactCertificate322_chunkChecks0_2

theorem compactCertificate322_chunkChecks1_0 :
    compactCertificate322.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (389 / 2) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27729712636 / 1000000000000) (27729712637 / 1000000000000), orderedInterval (49970479820 / 1000000000000) (49970479821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (573071278733489 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29648262969 / 1000000000000) (-29648260435 / 1000000000000), orderedInterval (59807415586 / 1000000000000) (59807418120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (185319477049937 / 800000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2287626884 / 1000000000000) (-2287626879 / 1000000000000), orderedInterval (52378381558 / 1000000000000) (52378381563 / 1000000000000)))) (orderedInterval (23877728228 / 1000000000000) (23877728262 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (167220769874323 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-121489931732 / 1000000000000) (-121489931467 / 1000000000000), orderedInterval (23072775957 / 1000000000000) (23072776223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (449178509429431 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1387064631 / 1000000000000) (-1387064623 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1219607030764827 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37228196465 / 1000000000000) (-37228196464 / 1000000000000), orderedInterval (-26434439944 / 1000000000000) (-26434439943 / 1000000000000)))) (orderedInterval (4479159852 / 1000000000000) (4479159880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (898357018859251 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38947727560 / 1000000000000) (-38947669883 / 1000000000000), orderedInterval (36386431168 / 1000000000000) (36386488845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1539350063820223 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28986367124 / 1000000000000) (28986388769 / 1000000000000), orderedInterval (-28569159937 / 1000000000000) (-28569138292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1133878289834557 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47305818154 / 1000000000000) (47305818207 / 1000000000000), orderedInterval (2739594363 / 1000000000000) (2739594416 / 1000000000000)))) (orderedInterval (1840011934 / 1000000000000) (1840013277 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks1_1 :
    compactCertificate322.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1739660886494611 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31796528489 / 1000000000000) (31796620114 / 1000000000000), orderedInterval (-21314673218 / 1000000000000) (-21314581593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1004393681116219 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26571566049 / 1000000000000) (26571566050 / 1000000000000), orderedInterval (42717332946 / 1000000000000) (42717332947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1782314212566071 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9626490440 / 1000000000000) (9626490441 / 1000000000000), orderedInterval (36541627938 / 1000000000000) (36541627939 / 1000000000000)))) (orderedInterval (24455046050 / 1000000000000) (24455082615 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1665269133098099 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26061383747 / 1000000000000) (26061393744 / 1000000000000), orderedInterval (-29185615332 / 1000000000000) (-29185605335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1188414630224867 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24693040800 / 1000000000000) (24693044103 / 1000000000000), orderedInterval (-39195204113 / 1000000000000) (-39195200809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1347535528288293 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43411565765 / 1000000000000) (-43411565678 / 1000000000000), orderedInterval (-2208115524 / 1000000000000) (-2208115437 / 1000000000000)))) (orderedInterval (-4514500004 / 1000000000000) (-4514499101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1123434635845717 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42424260344 / 1000000000000) (-42424235166 / 1000000000000), orderedInterval (21682733161 / 1000000000000) (21682758339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (992588571124057 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34385017933 / 1000000000000) (-34385017932 / 1000000000000), orderedInterval (-37121629736 / 1000000000000) (-37121629735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (287690855909643 / 800000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32549869686 / 1000000000000) (32549925230 / 1000000000000), orderedInterval (-26705971929 / 1000000000000) (-26705916385 / 1000000000000)))) (orderedInterval (1807596870 / 1000000000000) (1807599947 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks1_2 :
    compactCertificate322.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (795768047786321 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55005312528 / 1000000000000) (-55005311092 / 1000000000000), orderedInterval (13345569628 / 1000000000000) (13345571064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (674581386998281 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13168080762 / 1000000000000) (-13168080660 / 1000000000000), orderedInterval (60051700697 / 1000000000000) (60051700799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (422121710165443 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37203120738 / 1000000000000) (-37203116022 / 1000000000000), orderedInterval (68356429324 / 1000000000000) (68356434041 / 1000000000000)))) (orderedInterval (-3922276817 / 1000000000000) (-3922276448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (227018459640381 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88492482572 / 1000000000000) (88492482573 / 1000000000000), orderedInterval (57409504037 / 1000000000000) (57409504038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (616399279304143 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52145592420 / 1000000000000) (-52145592419 / 1000000000000), orderedInterval (-37408023573 / 1000000000000) (-37408023572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (841640518294511 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35780380951 / 1000000000000) (-35780380950 / 1000000000000), orderedInterval (-41692712768 / 1000000000000) (-41692712767 / 1000000000000)))) (orderedInterval (3819720981 / 1000000000000) (3819721002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (355878289834557 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82584117158 / 1000000000000) (82584117761 / 1000000000000), orderedInterval (-18773623127 / 1000000000000) (-18773622523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1446625490405597 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38436145470 / 1000000000000) (-38436145468 / 1000000000000), orderedInterval (-16767999097 / 1000000000000) (-16767999096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (966278785087123 / 4000000000000) 1 (IntervalRat.scale (389 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22418960056 / 1000000000000) (-22418960055 / 1000000000000), orderedInterval (-46135194352 / 1000000000000) (-46135194351 / 1000000000000)))) (orderedInterval (13237245819 / 1000000000000) (13237245897 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks1 :
    compactCertificate322.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate322.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate322_chunkChecks1_0
    compactCertificate322_chunkChecks1_1 compactCertificate322_chunkChecks1_2

theorem compactCertificate322_chunkChecks2_0 :
    compactCertificate322.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (389 / 2) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27729712636 / 1000000000000) (27729712637 / 1000000000000), orderedInterval (49970479820 / 1000000000000) (49970479821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (573071278733489 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29648262969 / 1000000000000) (-29648260435 / 1000000000000), orderedInterval (59807415586 / 1000000000000) (59807418120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (185319477049937 / 800000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2287626884 / 1000000000000) (-2287626879 / 1000000000000), orderedInterval (52378381558 / 1000000000000) (52378381563 / 1000000000000)))) (orderedInterval (-10773541109 / 1000000000000) (-10773541077 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (167220769874323 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-121489931732 / 1000000000000) (-121489931467 / 1000000000000), orderedInterval (23072775957 / 1000000000000) (23072776223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (449178509429431 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1387064631 / 1000000000000) (-1387064623 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1219607030764827 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37228196465 / 1000000000000) (-37228196464 / 1000000000000), orderedInterval (-26434439944 / 1000000000000) (-26434439943 / 1000000000000)))) (orderedInterval (-6570717086 / 1000000000000) (-6570717048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (898357018859251 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38947727560 / 1000000000000) (-38947669883 / 1000000000000), orderedInterval (36386431168 / 1000000000000) (36386488845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1539350063820223 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28986367124 / 1000000000000) (28986388769 / 1000000000000), orderedInterval (-28569159937 / 1000000000000) (-28569138292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1133878289834557 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47305818154 / 1000000000000) (47305818207 / 1000000000000), orderedInterval (2739594363 / 1000000000000) (2739594416 / 1000000000000)))) (orderedInterval (1062185304 / 1000000000000) (1062187961 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks2_1 :
    compactCertificate322.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1739660886494611 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31796528489 / 1000000000000) (31796620114 / 1000000000000), orderedInterval (-21314673218 / 1000000000000) (-21314581593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1004393681116219 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26571566049 / 1000000000000) (26571566050 / 1000000000000), orderedInterval (42717332946 / 1000000000000) (42717332947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1782314212566071 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9626490440 / 1000000000000) (9626490441 / 1000000000000), orderedInterval (36541627938 / 1000000000000) (36541627939 / 1000000000000)))) (orderedInterval (17660391794 / 1000000000000) (17660473728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1665269133098099 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26061383747 / 1000000000000) (26061393744 / 1000000000000), orderedInterval (-29185615332 / 1000000000000) (-29185605335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1188414630224867 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24693040800 / 1000000000000) (24693044103 / 1000000000000), orderedInterval (-39195204113 / 1000000000000) (-39195200809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1347535528288293 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43411565765 / 1000000000000) (-43411565678 / 1000000000000), orderedInterval (-2208115524 / 1000000000000) (-2208115437 / 1000000000000)))) (orderedInterval (-3928737765 / 1000000000000) (-3928736141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1123434635845717 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42424260344 / 1000000000000) (-42424235166 / 1000000000000), orderedInterval (21682733161 / 1000000000000) (21682758339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (992588571124057 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34385017933 / 1000000000000) (-34385017932 / 1000000000000), orderedInterval (-37121629736 / 1000000000000) (-37121629735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (287690855909643 / 800000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32549869686 / 1000000000000) (32549925230 / 1000000000000), orderedInterval (-26705971929 / 1000000000000) (-26705916385 / 1000000000000)))) (orderedInterval (-5039689366 / 1000000000000) (-5039683842 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks2_2 :
    compactCertificate322.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (795768047786321 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55005312528 / 1000000000000) (-55005311092 / 1000000000000), orderedInterval (13345569628 / 1000000000000) (13345571064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (674581386998281 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13168080762 / 1000000000000) (-13168080660 / 1000000000000), orderedInterval (60051700697 / 1000000000000) (60051700799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (422121710165443 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37203120738 / 1000000000000) (-37203116022 / 1000000000000), orderedInterval (68356429324 / 1000000000000) (68356434041 / 1000000000000)))) (orderedInterval (-9384862774 / 1000000000000) (-9384862439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (227018459640381 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88492482572 / 1000000000000) (88492482573 / 1000000000000), orderedInterval (57409504037 / 1000000000000) (57409504038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (616399279304143 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52145592420 / 1000000000000) (-52145592419 / 1000000000000), orderedInterval (-37408023573 / 1000000000000) (-37408023572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (841640518294511 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35780380951 / 1000000000000) (-35780380950 / 1000000000000), orderedInterval (-41692712768 / 1000000000000) (-41692712767 / 1000000000000)))) (orderedInterval (-3832248130 / 1000000000000) (-3832248108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (355878289834557 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82584117158 / 1000000000000) (82584117761 / 1000000000000), orderedInterval (-18773623127 / 1000000000000) (-18773622523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1446625490405597 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38436145470 / 1000000000000) (-38436145468 / 1000000000000), orderedInterval (-16767999097 / 1000000000000) (-16767999096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (966278785087123 / 4000000000000) 2 (IntervalRat.scale (389 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22418960056 / 1000000000000) (-22418960055 / 1000000000000), orderedInterval (-46135194352 / 1000000000000) (-46135194351 / 1000000000000)))) (orderedInterval (-17478388331 / 1000000000000) (-17478388217 / 1000000000000))) = true
  rfl'

theorem compactCertificate322_chunkChecks2 :
    compactCertificate322.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate322.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate322_chunkChecks2_0
    compactCertificate322_chunkChecks2_1 compactCertificate322_chunkChecks2_2

theorem compactCertificate322_chunkChecks3_0 :
    compactCertificate322.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (389 / 2) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27729712636 / 1000000000000) (27729712637 / 1000000000000), orderedInterval (49970479820 / 1000000000000) (49970479821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (573071278733489 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29648262969 / 1000000000000) (-29648260435 / 1000000000000), orderedInterval (59807415586 / 1000000000000) (59807418120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (185319477049937 / 800000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2287626884 / 1000000000000) (-2287626879 / 1000000000000), orderedInterval (52378381558 / 1000000000000) (52378381563 / 1000000000000)))) (orderedInterval (-25165853118 / 1000000000000) (-25165853087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (167220769874323 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-121489931732 / 1000000000000) (-121489931467 / 1000000000000), orderedInterval (23072775957 / 1000000000000) (23072776223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (449178509429431 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1387064631 / 1000000000000) (-1387064623 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1219607030764827 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37228196465 / 1000000000000) (-37228196464 / 1000000000000), orderedInterval (-26434439944 / 1000000000000) (-26434439943 / 1000000000000)))) (orderedInterval (-7731951186 / 1000000000000) (-7731951130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (898357018859251 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38947727560 / 1000000000000) (-38947669883 / 1000000000000), orderedInterval (36386431168 / 1000000000000) (36386488845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1539350063820223 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28986367124 / 1000000000000) (28986388769 / 1000000000000), orderedInterval (-28569159937 / 1000000000000) (-28569138292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1133878289834557 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47305818154 / 1000000000000) (47305818207 / 1000000000000), orderedInterval (2739594363 / 1000000000000) (2739594416 / 1000000000000)))) (orderedInterval (-7035992997 / 1000000000000) (-7035987747 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate322_chunkChecks3_1 :
    compactCertificate322.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1739660886494611 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31796528489 / 1000000000000) (31796620114 / 1000000000000), orderedInterval (-21314673218 / 1000000000000) (-21314581593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1004393681116219 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26571566049 / 1000000000000) (26571566050 / 1000000000000), orderedInterval (42717332946 / 1000000000000) (42717332947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1782314212566071 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9626490440 / 1000000000000) (9626490441 / 1000000000000), orderedInterval (36541627938 / 1000000000000) (36541627939 / 1000000000000)))) (orderedInterval (-111699065278 / 1000000000000) (-111698882085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1665269133098099 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26061383747 / 1000000000000) (26061393744 / 1000000000000), orderedInterval (-29185615332 / 1000000000000) (-29185605335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1188414630224867 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24693040800 / 1000000000000) (24693044103 / 1000000000000), orderedInterval (-39195204113 / 1000000000000) (-39195200809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1347535528288293 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43411565765 / 1000000000000) (-43411565678 / 1000000000000), orderedInterval (-2208115524 / 1000000000000) (-2208115437 / 1000000000000)))) (orderedInterval (8005542695 / 1000000000000) (8005545695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1123434635845717 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42424260344 / 1000000000000) (-42424235166 / 1000000000000), orderedInterval (21682733161 / 1000000000000) (21682758339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (992588571124057 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34385017933 / 1000000000000) (-34385017932 / 1000000000000), orderedInterval (-37121629736 / 1000000000000) (-37121629735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (287690855909643 / 800000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32549869686 / 1000000000000) (32549925230 / 1000000000000), orderedInterval (-26705971929 / 1000000000000) (-26705916385 / 1000000000000)))) (orderedInterval (-817733303 / 1000000000000) (-817723348 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate322_chunkChecks3_2 :
    compactCertificate322.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (795768047786321 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55005312528 / 1000000000000) (-55005311092 / 1000000000000), orderedInterval (13345569628 / 1000000000000) (13345571064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (674581386998281 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13168080762 / 1000000000000) (-13168080660 / 1000000000000), orderedInterval (60051700697 / 1000000000000) (60051700799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (422121710165443 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37203120738 / 1000000000000) (-37203116022 / 1000000000000), orderedInterval (68356429324 / 1000000000000) (68356434041 / 1000000000000)))) (orderedInterval (4191793201 / 1000000000000) (4191793519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (227018459640381 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88492482572 / 1000000000000) (88492482573 / 1000000000000), orderedInterval (57409504037 / 1000000000000) (57409504038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (616399279304143 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52145592420 / 1000000000000) (-52145592419 / 1000000000000), orderedInterval (-37408023573 / 1000000000000) (-37408023572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (841640518294511 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35780380951 / 1000000000000) (-35780380950 / 1000000000000), orderedInterval (-41692712768 / 1000000000000) (-41692712767 / 1000000000000)))) (orderedInterval (-4421226839 / 1000000000000) (-4421226817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (355878289834557 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82584117158 / 1000000000000) (82584117761 / 1000000000000), orderedInterval (-18773623127 / 1000000000000) (-18773622523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1446625490405597 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38436145470 / 1000000000000) (-38436145468 / 1000000000000), orderedInterval (-16767999097 / 1000000000000) (-16767999096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (966278785087123 / 4000000000000) 3 (IntervalRat.scale (389 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22418960056 / 1000000000000) (-22418960055 / 1000000000000), orderedInterval (-46135194352 / 1000000000000) (-46135194351 / 1000000000000)))) (orderedInterval (-25258128787 / 1000000000000) (-25258128613 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate322_chunkChecks3 :
    compactCertificate322.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate322.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate322_chunkChecks3_0
    compactCertificate322_chunkChecks3_1 compactCertificate322_chunkChecks3_2

theorem compactCertificate322_chunkChecks4_0 :
    compactCertificate322.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (389 / 2) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27729712636 / 1000000000000) (27729712637 / 1000000000000), orderedInterval (49970479820 / 1000000000000) (49970479821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (573071278733489 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29648262969 / 1000000000000) (-29648260435 / 1000000000000), orderedInterval (59807415586 / 1000000000000) (59807418120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (185319477049937 / 800000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2287626884 / 1000000000000) (-2287626879 / 1000000000000), orderedInterval (52378381558 / 1000000000000) (52378381563 / 1000000000000)))) (orderedInterval (10898142855 / 1000000000000) (10898142887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (167220769874323 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-121489931732 / 1000000000000) (-121489931467 / 1000000000000), orderedInterval (23072775957 / 1000000000000) (23072776223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (449178509429431 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1387064631 / 1000000000000) (-1387064623 / 1000000000000), orderedInterval (75287806643 / 1000000000000) (75287806651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1219607030764827 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-37228196465 / 1000000000000) (-37228196464 / 1000000000000), orderedInterval (-26434439944 / 1000000000000) (-26434439943 / 1000000000000)))) (orderedInterval (16058829658 / 1000000000000) (16058829744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (898357018859251 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38947727560 / 1000000000000) (-38947669883 / 1000000000000), orderedInterval (36386431168 / 1000000000000) (36386488845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1539350063820223 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28986367124 / 1000000000000) (28986388769 / 1000000000000), orderedInterval (-28569159937 / 1000000000000) (-28569138292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1133878289834557 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47305818154 / 1000000000000) (47305818207 / 1000000000000), orderedInterval (2739594363 / 1000000000000) (2739594416 / 1000000000000)))) (orderedInterval (-8471744008 / 1000000000000) (-8471733603 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate322_chunkChecks4_1 :
    compactCertificate322.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1739660886494611 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31796528489 / 1000000000000) (31796620114 / 1000000000000), orderedInterval (-21314673218 / 1000000000000) (-21314581593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1004393681116219 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26571566049 / 1000000000000) (26571566050 / 1000000000000), orderedInterval (42717332946 / 1000000000000) (42717332947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1782314212566071 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9626490440 / 1000000000000) (9626490441 / 1000000000000), orderedInterval (36541627938 / 1000000000000) (36541627939 / 1000000000000)))) (orderedInterval (-96936938342 / 1000000000000) (-96936527789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1665269133098099 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26061383747 / 1000000000000) (26061393744 / 1000000000000), orderedInterval (-29185615332 / 1000000000000) (-29185605335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1188414630224867 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24693040800 / 1000000000000) (24693044103 / 1000000000000), orderedInterval (-39195204113 / 1000000000000) (-39195200809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1347535528288293 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43411565765 / 1000000000000) (-43411565678 / 1000000000000), orderedInterval (-2208115524 / 1000000000000) (-2208115437 / 1000000000000)))) (orderedInterval (4732074071 / 1000000000000) (4732079777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1123434635845717 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42424260344 / 1000000000000) (-42424235166 / 1000000000000), orderedInterval (21682733161 / 1000000000000) (21682758339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (992588571124057 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34385017933 / 1000000000000) (-34385017932 / 1000000000000), orderedInterval (-37121629736 / 1000000000000) (-37121629735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (287690855909643 / 800000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32549869686 / 1000000000000) (32549925230 / 1000000000000), orderedInterval (-26705971929 / 1000000000000) (-26705916385 / 1000000000000)))) (orderedInterval (12830904017 / 1000000000000) (12830922099 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate322_chunkChecks4_2 :
    compactCertificate322.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (795768047786321 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55005312528 / 1000000000000) (-55005311092 / 1000000000000), orderedInterval (13345569628 / 1000000000000) (13345571064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (674581386998281 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13168080762 / 1000000000000) (-13168080660 / 1000000000000), orderedInterval (60051700697 / 1000000000000) (60051700799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (422121710165443 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37203120738 / 1000000000000) (-37203116022 / 1000000000000), orderedInterval (68356429324 / 1000000000000) (68356434041 / 1000000000000)))) (orderedInterval (9899271125 / 1000000000000) (9899271437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (227018459640381 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (88492482572 / 1000000000000) (88492482573 / 1000000000000), orderedInterval (57409504037 / 1000000000000) (57409504038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (616399279304143 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-52145592420 / 1000000000000) (-52145592419 / 1000000000000), orderedInterval (-37408023573 / 1000000000000) (-37408023572 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (841640518294511 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35780380951 / 1000000000000) (-35780380950 / 1000000000000), orderedInterval (-41692712768 / 1000000000000) (-41692712767 / 1000000000000)))) (orderedInterval (4255285349 / 1000000000000) (4255285372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (355878289834557 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82584117158 / 1000000000000) (82584117761 / 1000000000000), orderedInterval (-18773623127 / 1000000000000) (-18773622523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1446625490405597 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38436145470 / 1000000000000) (-38436145468 / 1000000000000), orderedInterval (-16767999097 / 1000000000000) (-16767999096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (966278785087123 / 4000000000000) 4 (IntervalRat.scale (389 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22418960056 / 1000000000000) (-22418960055 / 1000000000000), orderedInterval (-46135194352 / 1000000000000) (-46135194351 / 1000000000000)))) (orderedInterval (47690999928 / 1000000000000) (47691000208 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate322_chunkChecks4 :
    compactCertificate322.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate322.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate322_chunkChecks4_0
    compactCertificate322_chunkChecks4_1 compactCertificate322_chunkChecks4_2

theorem compactCertificate322_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate322.chunkCheck r b = true :=
  compactCertificate322.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate322_chunkChecks0
    · exact compactCertificate322_chunkChecks1
    · exact compactCertificate322_chunkChecks2
    · exact compactCertificate322_chunkChecks3
    · exact compactCertificate322_chunkChecks4)

theorem compactCertificate322_coefficient0 :
    compactCertificate322.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate322_coefficient1 :
    compactCertificate322.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate322_coefficient2 :
    compactCertificate322.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate322_coefficient3 :
    compactCertificate322.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate322_coefficient4 :
    compactCertificate322.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate322_coefficients : ∀ r : Fin 5,
    compactCertificate322.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate322_coefficient0
  · exact compactCertificate322_coefficient1
  · exact compactCertificate322_coefficient2
  · exact compactCertificate322_coefficient3
  · exact compactCertificate322_coefficient4

theorem compactCertificate322_lower : (1 : ℚ) ≤ compactCertificate322.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate322, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate322_proves {t : ℝ} (ht : t ∈ compactCertificate322.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate322.proves compactCertificate322_states compactCertificate322_chunks
    compactCertificate322_coefficients compactCertificate322_lower ht

end Erdos232
