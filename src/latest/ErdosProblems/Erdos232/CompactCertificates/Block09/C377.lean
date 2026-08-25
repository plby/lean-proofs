/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate377 : CompactCertificate where
  left := 248
  right := 249
  center := 497 / 2
  grid := fun i =>
    match i.val with
    | 0 => 79
    | 1 => 58
    | 2 => 94
    | 3 => 17
    | 4 => 46
    | 5 => 124
    | 6 => 91
    | 7 => 157
    | 8 => 115
    | 9 => 177
    | 10 => 102
    | 11 => 181
    | 12 => 169
    | 13 => 121
    | 14 => 137
    | 15 => 114
    | 16 => 101
    | 17 => 146
    | 18 => 81
    | 19 => 69
    | 20 => 43
    | 21 => 23
    | 22 => 63
    | 23 => 86
    | 24 => 36
    | 25 => 147
    | _ => 98
  point := fun i =>
    match i.val with
    | 0 => 497 / 2
    | 1 => 732175901106797 / 4000000000000
    | 2 => 236770642914701 / 800000000000
    | 3 => 213647101870279 / 4000000000000
    | 4 => 573886167574363 / 4000000000000
    | 5 => 1558212581722671 / 4000000000000
    | 6 => 1147772335149223 / 4000000000000
    | 7 => 1966727459430979 / 4000000000000
    | 8 => 1448682545109961 / 4000000000000
    | 9 => 2222651569634503 / 4000000000000
    | 10 => 1283248482043087 / 4000000000000
    | 11 => 2277146950245083 / 4000000000000
    | 12 => 2127606064652327 / 4000000000000
    | 13 => 1518360080261591 / 4000000000000
    | 14 => 1721658502723089 / 4000000000000
    | 15 => 1435339367648641 / 4000000000000
    | 16 => 1268165860793461 / 4000000000000
    | 17 => 367563895596639 / 800000000000
    | 18 => 1016701079048333 / 4000000000000
    | 19 => 861868764365413 / 4000000000000
    | 20 => 539317454890039 / 4000000000000
    | 21 => 290046720928713 / 4000000000000
    | 22 => 787533269445139 / 4000000000000
    | 23 => 1075309351137203 / 4000000000000
    | 24 => 454682545109961 / 4000000000000
    | 25 => 1848259302651881 / 4000000000000
    | _ => 1234551558324679 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-45086923917 / 1000000000000) (-45086923916 / 1000000000000), orderedInterval (-22909639565 / 1000000000000) (-22909639564 / 1000000000000))
    | 1 => (orderedInterval (58913038875 / 1000000000000) (58913038991 / 1000000000000), orderedInterval (-2844528964 / 1000000000000) (-2844528848 / 1000000000000))
    | 2 => (orderedInterval (45974090397 / 1000000000000) (45974090417 / 1000000000000), orderedInterval (6037001891 / 1000000000000) (6037001911 / 1000000000000))
    | 3 => (orderedInterval (-77378404859 / 1000000000000) (-77378404858 / 1000000000000), orderedInterval (-76293043648 / 1000000000000) (-76293043647 / 1000000000000))
    | 4 => (orderedInterval (-16944034640 / 1000000000000) (-16944034427 / 1000000000000), orderedInterval (64480923273 / 1000000000000) (64480923486 / 1000000000000))
    | 5 => (orderedInterval (28451573148 / 1000000000000) (28451573149 / 1000000000000), orderedInterval (28681748837 / 1000000000000) (28681748838 / 1000000000000))
    | 6 => (orderedInterval (-45366548990 / 1000000000000) (-45366545436 / 1000000000000), orderedInterval (12747942537 / 1000000000000) (12747946091 / 1000000000000))
    | 7 => (orderedInterval (24868600488 / 1000000000000) (24868610036 / 1000000000000), orderedInterval (-26031684500 / 1000000000000) (-26031674951 / 1000000000000))
    | 8 => (orderedInterval (-41709189629 / 1000000000000) (-41709188848 / 1000000000000), orderedInterval (4315688844 / 1000000000000) (4315689625 / 1000000000000))
    | 9 => (orderedInterval (-12748529664 / 1000000000000) (-12748529663 / 1000000000000), orderedInterval (-31344063285 / 1000000000000) (-31344063284 / 1000000000000))
    | 10 => (orderedInterval (40745202018 / 1000000000000) (40745202019 / 1000000000000), orderedInterval (17942815682 / 1000000000000) (17942815683 / 1000000000000))
    | 11 => (orderedInterval (-33170672211 / 1000000000000) (-33170672053 / 1000000000000), orderedInterval (-4211412209 / 1000000000000) (-4211412050 / 1000000000000))
    | 12 => (orderedInterval (-33994519617 / 1000000000000) (-33994514268 / 1000000000000), orderedInterval (6454381825 / 1000000000000) (6454387173 / 1000000000000))
    | 13 => (orderedInterval (-9829123397 / 1000000000000) (-9829123396 / 1000000000000), orderedInterval (-39742735002 / 1000000000000) (-39742735001 / 1000000000000))
    | 14 => (orderedInterval (-27629925154 / 1000000000000) (-27629925153 / 1000000000000), orderedInterval (-26719951711 / 1000000000000) (-26719951710 / 1000000000000))
    | 15 => (orderedInterval (41940465935 / 1000000000000) (41940465993 / 1000000000000), orderedInterval (3830768469 / 1000000000000) (3830768526 / 1000000000000))
    | 16 => (orderedInterval (-22483398088 / 1000000000000) (-22483398087 / 1000000000000), orderedInterval (-38726632450 / 1000000000000) (-38726632449 / 1000000000000))
    | 17 => (orderedInterval (37223404860 / 1000000000000) (37223405250 / 1000000000000), orderedInterval (83377332 / 1000000000000) (83377722 / 1000000000000))
    | 18 => (orderedInterval (-23604841000 / 1000000000000) (-23604840999 / 1000000000000), orderedInterval (-44083634251 / 1000000000000) (-44083634250 / 1000000000000))
    | 19 => (orderedInterval (26908626623 / 1000000000000) (26908629802 / 1000000000000), orderedInterval (-47290948682 / 1000000000000) (-47290945503 / 1000000000000))
    | 20 => (orderedInterval (-34461288399 / 1000000000000) (-34461288398 / 1000000000000), orderedInterval (-59320551586 / 1000000000000) (-59320551585 / 1000000000000))
    | 21 => (orderedInterval (-80745057701 / 1000000000000) (-80745057700 / 1000000000000), orderedInterval (-46979369879 / 1000000000000) (-46979369878 / 1000000000000))
    | 22 => (orderedInterval (14192587594 / 1000000000000) (14192587733 / 1000000000000), orderedInterval (-55100252940 / 1000000000000) (-55100252802 / 1000000000000))
    | 23 => (orderedInterval (-26042742391 / 1000000000000) (-26042738451 / 1000000000000), orderedInterval (41156995413 / 1000000000000) (41156999353 / 1000000000000))
    | 24 => (orderedInterval (73142220002 / 1000000000000) (73142220004 / 1000000000000), orderedInterval (15512771499 / 1000000000000) (15512771501 / 1000000000000))
    | 25 => (orderedInterval (-31932436875 / 1000000000000) (-31932436874 / 1000000000000), orderedInterval (-18888729008 / 1000000000000) (-18888729007 / 1000000000000))
    | _ => (orderedInterval (45403583716 / 1000000000000) (45403583823 / 1000000000000), orderedInterval (1016053009 / 1000000000000) (1016053115 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14624111026 / 1000000000000) (-14624111005 / 1000000000000)
      | 1 => orderedInterval (-1801767594 / 1000000000000) (-1801767556 / 1000000000000)
      | 2 => orderedInterval (-1775076261 / 1000000000000) (-1775075933 / 1000000000000)
      | 3 => orderedInterval (568737427 / 1000000000000) (568737548 / 1000000000000)
      | 4 => orderedInterval (-175940868 / 1000000000000) (-175940741 / 1000000000000)
      | 5 => orderedInterval (2724031005 / 1000000000000) (2724031040 / 1000000000000)
      | 6 => orderedInterval (1129311793 / 1000000000000) (1129312036 / 1000000000000)
      | 7 => orderedInterval (3164867690 / 1000000000000) (3164868025 / 1000000000000)
      | _ => orderedInterval (-5478634382 / 1000000000000) (-5478634293 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8678181780 / 1000000000000) (-8678181758 / 1000000000000)
      | 1 => orderedInterval (-1659164147 / 1000000000000) (-1659164107 / 1000000000000)
      | 2 => orderedInterval (1740670837 / 1000000000000) (1740671472 / 1000000000000)
      | 3 => orderedInterval (12798457333 / 1000000000000) (12798457590 / 1000000000000)
      | 4 => orderedInterval (-5755928859 / 1000000000000) (-5755928604 / 1000000000000)
      | 5 => orderedInterval (2895294148 / 1000000000000) (2895294202 / 1000000000000)
      | 6 => orderedInterval (8482662046 / 1000000000000) (8482662261 / 1000000000000)
      | 7 => orderedInterval (-2168713920 / 1000000000000) (-2168713563 / 1000000000000)
      | _ => orderedInterval (2664996320 / 1000000000000) (2664996442 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (13781162266 / 1000000000000) (13781162292 / 1000000000000)
      | 1 => orderedInterval (5144534221 / 1000000000000) (5144534271 / 1000000000000)
      | 2 => orderedInterval (5137020690 / 1000000000000) (5137021929 / 1000000000000)
      | 3 => orderedInterval (8338061872 / 1000000000000) (8338062429 / 1000000000000)
      | 4 => orderedInterval (-1039250632 / 1000000000000) (-1039250109 / 1000000000000)
      | 5 => orderedInterval (-6373859205 / 1000000000000) (-6373859117 / 1000000000000)
      | 6 => orderedInterval (-2507431889 / 1000000000000) (-2507431697 / 1000000000000)
      | 7 => orderedInterval (-2251875140 / 1000000000000) (-2251874756 / 1000000000000)
      | _ => orderedInterval (4050978876 / 1000000000000) (4050979051 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8437087898 / 1000000000000) (8437087928 / 1000000000000)
      | 1 => orderedInterval (7372724317 / 1000000000000) (7372724390 / 1000000000000)
      | 2 => orderedInterval (-6562901665 / 1000000000000) (-6562899242 / 1000000000000)
      | 3 => orderedInterval (-57964352620 / 1000000000000) (-57964351387 / 1000000000000)
      | 4 => orderedInterval (13839168933 / 1000000000000) (13839170017 / 1000000000000)
      | 5 => orderedInterval (-4723315814 / 1000000000000) (-4723315669 / 1000000000000)
      | 6 => orderedInterval (-8968848168 / 1000000000000) (-8968847996 / 1000000000000)
      | 7 => orderedInterval (3359099225 / 1000000000000) (3359099639 / 1000000000000)
      | _ => orderedInterval (-9544729535 / 1000000000000) (-9544729276 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-12348732565 / 1000000000000) (-12348732530 / 1000000000000)
      | 1 => orderedInterval (-12340651756 / 1000000000000) (-12340651646 / 1000000000000)
      | 2 => orderedInterval (-16250928501 / 1000000000000) (-16250923738 / 1000000000000)
      | 3 => orderedInterval (-64394738096 / 1000000000000) (-64394735341 / 1000000000000)
      | 4 => orderedInterval (8968454949 / 1000000000000) (8968457219 / 1000000000000)
      | 5 => orderedInterval (16690100003 / 1000000000000) (16690100249 / 1000000000000)
      | 6 => orderedInterval (3245081134 / 1000000000000) (3245081290 / 1000000000000)
      | 7 => orderedInterval (2590396090 / 1000000000000) (2590396537 / 1000000000000)
      | _ => orderedInterval (10897361360 / 1000000000000) (10897361763 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-16268582216 / 1000000000000) (-16268580879 / 1000000000000)
    | 1 => orderedInterval (10320091978 / 1000000000000) (10320093935 / 1000000000000)
    | 2 => orderedInterval (24279341059 / 1000000000000) (24279344293 / 1000000000000)
    | 3 => orderedInterval (-54756067429 / 1000000000000) (-54756061596 / 1000000000000)
    | _ => orderedInterval (-62943657382 / 1000000000000) (-62943646197 / 1000000000000)

theorem compactCertificate377_stateChecks0 :
    compactCertificate377.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (497 / 2)) (orderedInterval (-45086923917 / 1000000000000) (-45086923916 / 1000000000000), orderedInterval (-22909639565 / 1000000000000) (-22909639564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (732175901106797 / 4000000000000)) (orderedInterval (58913038875 / 1000000000000) (58913038991 / 1000000000000), orderedInterval (-2844528964 / 1000000000000) (-2844528848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (236770642914701 / 800000000000)) (orderedInterval (45974090397 / 1000000000000) (45974090417 / 1000000000000), orderedInterval (6037001891 / 1000000000000) (6037001911 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks1 :
    compactCertificate377.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (213647101870279 / 4000000000000)) (orderedInterval (-77378404859 / 1000000000000) (-77378404858 / 1000000000000), orderedInterval (-76293043648 / 1000000000000) (-76293043647 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (573886167574363 / 4000000000000)) (orderedInterval (-16944034640 / 1000000000000) (-16944034427 / 1000000000000), orderedInterval (64480923273 / 1000000000000) (64480923486 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1558212581722671 / 4000000000000)) (orderedInterval (28451573148 / 1000000000000) (28451573149 / 1000000000000), orderedInterval (28681748837 / 1000000000000) (28681748838 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks2 :
    compactCertificate377.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1147772335149223 / 4000000000000)) (orderedInterval (-45366548990 / 1000000000000) (-45366545436 / 1000000000000), orderedInterval (12747942537 / 1000000000000) (12747946091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1966727459430979 / 4000000000000)) (orderedInterval (24868600488 / 1000000000000) (24868610036 / 1000000000000), orderedInterval (-26031684500 / 1000000000000) (-26031674951 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1448682545109961 / 4000000000000)) (orderedInterval (-41709189629 / 1000000000000) (-41709188848 / 1000000000000), orderedInterval (4315688844 / 1000000000000) (4315689625 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks3 :
    compactCertificate377.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2222651569634503 / 4000000000000)) (orderedInterval (-12748529664 / 1000000000000) (-12748529663 / 1000000000000), orderedInterval (-31344063285 / 1000000000000) (-31344063284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1283248482043087 / 4000000000000)) (orderedInterval (40745202018 / 1000000000000) (40745202019 / 1000000000000), orderedInterval (17942815682 / 1000000000000) (17942815683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2277146950245083 / 4000000000000)) (orderedInterval (-33170672211 / 1000000000000) (-33170672053 / 1000000000000), orderedInterval (-4211412209 / 1000000000000) (-4211412050 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks4 :
    compactCertificate377.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2127606064652327 / 4000000000000)) (orderedInterval (-33994519617 / 1000000000000) (-33994514268 / 1000000000000), orderedInterval (6454381825 / 1000000000000) (6454387173 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1518360080261591 / 4000000000000)) (orderedInterval (-9829123397 / 1000000000000) (-9829123396 / 1000000000000), orderedInterval (-39742735002 / 1000000000000) (-39742735001 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1721658502723089 / 4000000000000)) (orderedInterval (-27629925154 / 1000000000000) (-27629925153 / 1000000000000), orderedInterval (-26719951711 / 1000000000000) (-26719951710 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks5 :
    compactCertificate377.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1435339367648641 / 4000000000000)) (orderedInterval (41940465935 / 1000000000000) (41940465993 / 1000000000000), orderedInterval (3830768469 / 1000000000000) (3830768526 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1268165860793461 / 4000000000000)) (orderedInterval (-22483398088 / 1000000000000) (-22483398087 / 1000000000000), orderedInterval (-38726632450 / 1000000000000) (-38726632449 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (367563895596639 / 800000000000)) (orderedInterval (37223404860 / 1000000000000) (37223405250 / 1000000000000), orderedInterval (83377332 / 1000000000000) (83377722 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks6 :
    compactCertificate377.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1016701079048333 / 4000000000000)) (orderedInterval (-23604841000 / 1000000000000) (-23604840999 / 1000000000000), orderedInterval (-44083634251 / 1000000000000) (-44083634250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (861868764365413 / 4000000000000)) (orderedInterval (26908626623 / 1000000000000) (26908629802 / 1000000000000), orderedInterval (-47290948682 / 1000000000000) (-47290945503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (539317454890039 / 4000000000000)) (orderedInterval (-34461288399 / 1000000000000) (-34461288398 / 1000000000000), orderedInterval (-59320551586 / 1000000000000) (-59320551585 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks7 :
    compactCertificate377.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (290046720928713 / 4000000000000)) (orderedInterval (-80745057701 / 1000000000000) (-80745057700 / 1000000000000), orderedInterval (-46979369879 / 1000000000000) (-46979369878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (787533269445139 / 4000000000000)) (orderedInterval (14192587594 / 1000000000000) (14192587733 / 1000000000000), orderedInterval (-55100252940 / 1000000000000) (-55100252802 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1075309351137203 / 4000000000000)) (orderedInterval (-26042742391 / 1000000000000) (-26042738451 / 1000000000000), orderedInterval (41156995413 / 1000000000000) (41156999353 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_stateChecks8 :
    compactCertificate377.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (454682545109961 / 4000000000000)) (orderedInterval (73142220002 / 1000000000000) (73142220004 / 1000000000000), orderedInterval (15512771499 / 1000000000000) (15512771501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1848259302651881 / 4000000000000)) (orderedInterval (-31932436875 / 1000000000000) (-31932436874 / 1000000000000), orderedInterval (-18888729008 / 1000000000000) (-18888729007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1234551558324679 / 4000000000000)) (orderedInterval (45403583716 / 1000000000000) (45403583823 / 1000000000000), orderedInterval (1016053009 / 1000000000000) (1016053115 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_states : ∀ j,
    BesselStateValid (compactCertificate377.point j) (compactCertificate377.state j) :=
  compactCertificate377.statesValid_of_checks3 compactCertificate377_stateChecks0
    compactCertificate377_stateChecks1 compactCertificate377_stateChecks2
    compactCertificate377_stateChecks3 compactCertificate377_stateChecks4
    compactCertificate377_stateChecks5 compactCertificate377_stateChecks6
    compactCertificate377_stateChecks7 compactCertificate377_stateChecks8

theorem compactCertificate377_chunkChecks0_0 :
    compactCertificate377.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (497 / 2) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45086923917 / 1000000000000) (-45086923916 / 1000000000000), orderedInterval (-22909639565 / 1000000000000) (-22909639564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (732175901106797 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (58913038875 / 1000000000000) (58913038991 / 1000000000000), orderedInterval (-2844528964 / 1000000000000) (-2844528848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (236770642914701 / 800000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45974090397 / 1000000000000) (45974090417 / 1000000000000), orderedInterval (6037001891 / 1000000000000) (6037001911 / 1000000000000)))) (orderedInterval (-14624111026 / 1000000000000) (-14624111005 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (213647101870279 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77378404859 / 1000000000000) (-77378404858 / 1000000000000), orderedInterval (-76293043648 / 1000000000000) (-76293043647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (573886167574363 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16944034640 / 1000000000000) (-16944034427 / 1000000000000), orderedInterval (64480923273 / 1000000000000) (64480923486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1558212581722671 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28451573148 / 1000000000000) (28451573149 / 1000000000000), orderedInterval (28681748837 / 1000000000000) (28681748838 / 1000000000000)))) (orderedInterval (-1801767594 / 1000000000000) (-1801767556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1147772335149223 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45366548990 / 1000000000000) (-45366545436 / 1000000000000), orderedInterval (12747942537 / 1000000000000) (12747946091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1966727459430979 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24868600488 / 1000000000000) (24868610036 / 1000000000000), orderedInterval (-26031684500 / 1000000000000) (-26031674951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1448682545109961 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41709189629 / 1000000000000) (-41709188848 / 1000000000000), orderedInterval (4315688844 / 1000000000000) (4315689625 / 1000000000000)))) (orderedInterval (-1775076261 / 1000000000000) (-1775075933 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks0_1 :
    compactCertificate377.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2222651569634503 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12748529664 / 1000000000000) (-12748529663 / 1000000000000), orderedInterval (-31344063285 / 1000000000000) (-31344063284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1283248482043087 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40745202018 / 1000000000000) (40745202019 / 1000000000000), orderedInterval (17942815682 / 1000000000000) (17942815683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2277146950245083 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33170672211 / 1000000000000) (-33170672053 / 1000000000000), orderedInterval (-4211412209 / 1000000000000) (-4211412050 / 1000000000000)))) (orderedInterval (568737427 / 1000000000000) (568737548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2127606064652327 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33994519617 / 1000000000000) (-33994514268 / 1000000000000), orderedInterval (6454381825 / 1000000000000) (6454387173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1518360080261591 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9829123397 / 1000000000000) (-9829123396 / 1000000000000), orderedInterval (-39742735002 / 1000000000000) (-39742735001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1721658502723089 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27629925154 / 1000000000000) (-27629925153 / 1000000000000), orderedInterval (-26719951711 / 1000000000000) (-26719951710 / 1000000000000)))) (orderedInterval (-175940868 / 1000000000000) (-175940741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1435339367648641 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (41940465935 / 1000000000000) (41940465993 / 1000000000000), orderedInterval (3830768469 / 1000000000000) (3830768526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1268165860793461 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22483398088 / 1000000000000) (-22483398087 / 1000000000000), orderedInterval (-38726632450 / 1000000000000) (-38726632449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (367563895596639 / 800000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37223404860 / 1000000000000) (37223405250 / 1000000000000), orderedInterval (83377332 / 1000000000000) (83377722 / 1000000000000)))) (orderedInterval (2724031005 / 1000000000000) (2724031040 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks0_2 :
    compactCertificate377.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1016701079048333 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23604841000 / 1000000000000) (-23604840999 / 1000000000000), orderedInterval (-44083634251 / 1000000000000) (-44083634250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (861868764365413 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26908626623 / 1000000000000) (26908629802 / 1000000000000), orderedInterval (-47290948682 / 1000000000000) (-47290945503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (539317454890039 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34461288399 / 1000000000000) (-34461288398 / 1000000000000), orderedInterval (-59320551586 / 1000000000000) (-59320551585 / 1000000000000)))) (orderedInterval (1129311793 / 1000000000000) (1129312036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (290046720928713 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80745057701 / 1000000000000) (-80745057700 / 1000000000000), orderedInterval (-46979369879 / 1000000000000) (-46979369878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (787533269445139 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14192587594 / 1000000000000) (14192587733 / 1000000000000), orderedInterval (-55100252940 / 1000000000000) (-55100252802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1075309351137203 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26042742391 / 1000000000000) (-26042738451 / 1000000000000), orderedInterval (41156995413 / 1000000000000) (41156999353 / 1000000000000)))) (orderedInterval (3164867690 / 1000000000000) (3164868025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (454682545109961 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (73142220002 / 1000000000000) (73142220004 / 1000000000000), orderedInterval (15512771499 / 1000000000000) (15512771501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1848259302651881 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31932436875 / 1000000000000) (-31932436874 / 1000000000000), orderedInterval (-18888729008 / 1000000000000) (-18888729007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1234551558324679 / 4000000000000) 0 (IntervalRat.scale (497 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45403583716 / 1000000000000) (45403583823 / 1000000000000), orderedInterval (1016053009 / 1000000000000) (1016053115 / 1000000000000)))) (orderedInterval (-5478634382 / 1000000000000) (-5478634293 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks0 :
    compactCertificate377.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate377.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate377_chunkChecks0_0
    compactCertificate377_chunkChecks0_1 compactCertificate377_chunkChecks0_2

theorem compactCertificate377_chunkChecks1_0 :
    compactCertificate377.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (497 / 2) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45086923917 / 1000000000000) (-45086923916 / 1000000000000), orderedInterval (-22909639565 / 1000000000000) (-22909639564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (732175901106797 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (58913038875 / 1000000000000) (58913038991 / 1000000000000), orderedInterval (-2844528964 / 1000000000000) (-2844528848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (236770642914701 / 800000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45974090397 / 1000000000000) (45974090417 / 1000000000000), orderedInterval (6037001891 / 1000000000000) (6037001911 / 1000000000000)))) (orderedInterval (-8678181780 / 1000000000000) (-8678181758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (213647101870279 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77378404859 / 1000000000000) (-77378404858 / 1000000000000), orderedInterval (-76293043648 / 1000000000000) (-76293043647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (573886167574363 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16944034640 / 1000000000000) (-16944034427 / 1000000000000), orderedInterval (64480923273 / 1000000000000) (64480923486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1558212581722671 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28451573148 / 1000000000000) (28451573149 / 1000000000000), orderedInterval (28681748837 / 1000000000000) (28681748838 / 1000000000000)))) (orderedInterval (-1659164147 / 1000000000000) (-1659164107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1147772335149223 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45366548990 / 1000000000000) (-45366545436 / 1000000000000), orderedInterval (12747942537 / 1000000000000) (12747946091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1966727459430979 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24868600488 / 1000000000000) (24868610036 / 1000000000000), orderedInterval (-26031684500 / 1000000000000) (-26031674951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1448682545109961 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41709189629 / 1000000000000) (-41709188848 / 1000000000000), orderedInterval (4315688844 / 1000000000000) (4315689625 / 1000000000000)))) (orderedInterval (1740670837 / 1000000000000) (1740671472 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks1_1 :
    compactCertificate377.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2222651569634503 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12748529664 / 1000000000000) (-12748529663 / 1000000000000), orderedInterval (-31344063285 / 1000000000000) (-31344063284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1283248482043087 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40745202018 / 1000000000000) (40745202019 / 1000000000000), orderedInterval (17942815682 / 1000000000000) (17942815683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2277146950245083 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33170672211 / 1000000000000) (-33170672053 / 1000000000000), orderedInterval (-4211412209 / 1000000000000) (-4211412050 / 1000000000000)))) (orderedInterval (12798457333 / 1000000000000) (12798457590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2127606064652327 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33994519617 / 1000000000000) (-33994514268 / 1000000000000), orderedInterval (6454381825 / 1000000000000) (6454387173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1518360080261591 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9829123397 / 1000000000000) (-9829123396 / 1000000000000), orderedInterval (-39742735002 / 1000000000000) (-39742735001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1721658502723089 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27629925154 / 1000000000000) (-27629925153 / 1000000000000), orderedInterval (-26719951711 / 1000000000000) (-26719951710 / 1000000000000)))) (orderedInterval (-5755928859 / 1000000000000) (-5755928604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1435339367648641 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (41940465935 / 1000000000000) (41940465993 / 1000000000000), orderedInterval (3830768469 / 1000000000000) (3830768526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1268165860793461 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22483398088 / 1000000000000) (-22483398087 / 1000000000000), orderedInterval (-38726632450 / 1000000000000) (-38726632449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (367563895596639 / 800000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37223404860 / 1000000000000) (37223405250 / 1000000000000), orderedInterval (83377332 / 1000000000000) (83377722 / 1000000000000)))) (orderedInterval (2895294148 / 1000000000000) (2895294202 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks1_2 :
    compactCertificate377.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1016701079048333 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23604841000 / 1000000000000) (-23604840999 / 1000000000000), orderedInterval (-44083634251 / 1000000000000) (-44083634250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (861868764365413 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26908626623 / 1000000000000) (26908629802 / 1000000000000), orderedInterval (-47290948682 / 1000000000000) (-47290945503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (539317454890039 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34461288399 / 1000000000000) (-34461288398 / 1000000000000), orderedInterval (-59320551586 / 1000000000000) (-59320551585 / 1000000000000)))) (orderedInterval (8482662046 / 1000000000000) (8482662261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (290046720928713 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80745057701 / 1000000000000) (-80745057700 / 1000000000000), orderedInterval (-46979369879 / 1000000000000) (-46979369878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (787533269445139 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14192587594 / 1000000000000) (14192587733 / 1000000000000), orderedInterval (-55100252940 / 1000000000000) (-55100252802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1075309351137203 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26042742391 / 1000000000000) (-26042738451 / 1000000000000), orderedInterval (41156995413 / 1000000000000) (41156999353 / 1000000000000)))) (orderedInterval (-2168713920 / 1000000000000) (-2168713563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (454682545109961 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (73142220002 / 1000000000000) (73142220004 / 1000000000000), orderedInterval (15512771499 / 1000000000000) (15512771501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1848259302651881 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31932436875 / 1000000000000) (-31932436874 / 1000000000000), orderedInterval (-18888729008 / 1000000000000) (-18888729007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1234551558324679 / 4000000000000) 1 (IntervalRat.scale (497 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45403583716 / 1000000000000) (45403583823 / 1000000000000), orderedInterval (1016053009 / 1000000000000) (1016053115 / 1000000000000)))) (orderedInterval (2664996320 / 1000000000000) (2664996442 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks1 :
    compactCertificate377.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate377.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate377_chunkChecks1_0
    compactCertificate377_chunkChecks1_1 compactCertificate377_chunkChecks1_2

theorem compactCertificate377_chunkChecks2_0 :
    compactCertificate377.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (497 / 2) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45086923917 / 1000000000000) (-45086923916 / 1000000000000), orderedInterval (-22909639565 / 1000000000000) (-22909639564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (732175901106797 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (58913038875 / 1000000000000) (58913038991 / 1000000000000), orderedInterval (-2844528964 / 1000000000000) (-2844528848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (236770642914701 / 800000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45974090397 / 1000000000000) (45974090417 / 1000000000000), orderedInterval (6037001891 / 1000000000000) (6037001911 / 1000000000000)))) (orderedInterval (13781162266 / 1000000000000) (13781162292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (213647101870279 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77378404859 / 1000000000000) (-77378404858 / 1000000000000), orderedInterval (-76293043648 / 1000000000000) (-76293043647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (573886167574363 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16944034640 / 1000000000000) (-16944034427 / 1000000000000), orderedInterval (64480923273 / 1000000000000) (64480923486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1558212581722671 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28451573148 / 1000000000000) (28451573149 / 1000000000000), orderedInterval (28681748837 / 1000000000000) (28681748838 / 1000000000000)))) (orderedInterval (5144534221 / 1000000000000) (5144534271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1147772335149223 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45366548990 / 1000000000000) (-45366545436 / 1000000000000), orderedInterval (12747942537 / 1000000000000) (12747946091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1966727459430979 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24868600488 / 1000000000000) (24868610036 / 1000000000000), orderedInterval (-26031684500 / 1000000000000) (-26031674951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1448682545109961 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41709189629 / 1000000000000) (-41709188848 / 1000000000000), orderedInterval (4315688844 / 1000000000000) (4315689625 / 1000000000000)))) (orderedInterval (5137020690 / 1000000000000) (5137021929 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks2_1 :
    compactCertificate377.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2222651569634503 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12748529664 / 1000000000000) (-12748529663 / 1000000000000), orderedInterval (-31344063285 / 1000000000000) (-31344063284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1283248482043087 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40745202018 / 1000000000000) (40745202019 / 1000000000000), orderedInterval (17942815682 / 1000000000000) (17942815683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2277146950245083 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33170672211 / 1000000000000) (-33170672053 / 1000000000000), orderedInterval (-4211412209 / 1000000000000) (-4211412050 / 1000000000000)))) (orderedInterval (8338061872 / 1000000000000) (8338062429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2127606064652327 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33994519617 / 1000000000000) (-33994514268 / 1000000000000), orderedInterval (6454381825 / 1000000000000) (6454387173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1518360080261591 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9829123397 / 1000000000000) (-9829123396 / 1000000000000), orderedInterval (-39742735002 / 1000000000000) (-39742735001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1721658502723089 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27629925154 / 1000000000000) (-27629925153 / 1000000000000), orderedInterval (-26719951711 / 1000000000000) (-26719951710 / 1000000000000)))) (orderedInterval (-1039250632 / 1000000000000) (-1039250109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1435339367648641 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (41940465935 / 1000000000000) (41940465993 / 1000000000000), orderedInterval (3830768469 / 1000000000000) (3830768526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1268165860793461 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22483398088 / 1000000000000) (-22483398087 / 1000000000000), orderedInterval (-38726632450 / 1000000000000) (-38726632449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (367563895596639 / 800000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37223404860 / 1000000000000) (37223405250 / 1000000000000), orderedInterval (83377332 / 1000000000000) (83377722 / 1000000000000)))) (orderedInterval (-6373859205 / 1000000000000) (-6373859117 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks2_2 :
    compactCertificate377.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1016701079048333 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23604841000 / 1000000000000) (-23604840999 / 1000000000000), orderedInterval (-44083634251 / 1000000000000) (-44083634250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (861868764365413 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26908626623 / 1000000000000) (26908629802 / 1000000000000), orderedInterval (-47290948682 / 1000000000000) (-47290945503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (539317454890039 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34461288399 / 1000000000000) (-34461288398 / 1000000000000), orderedInterval (-59320551586 / 1000000000000) (-59320551585 / 1000000000000)))) (orderedInterval (-2507431889 / 1000000000000) (-2507431697 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (290046720928713 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80745057701 / 1000000000000) (-80745057700 / 1000000000000), orderedInterval (-46979369879 / 1000000000000) (-46979369878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (787533269445139 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14192587594 / 1000000000000) (14192587733 / 1000000000000), orderedInterval (-55100252940 / 1000000000000) (-55100252802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1075309351137203 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26042742391 / 1000000000000) (-26042738451 / 1000000000000), orderedInterval (41156995413 / 1000000000000) (41156999353 / 1000000000000)))) (orderedInterval (-2251875140 / 1000000000000) (-2251874756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (454682545109961 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (73142220002 / 1000000000000) (73142220004 / 1000000000000), orderedInterval (15512771499 / 1000000000000) (15512771501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1848259302651881 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31932436875 / 1000000000000) (-31932436874 / 1000000000000), orderedInterval (-18888729008 / 1000000000000) (-18888729007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1234551558324679 / 4000000000000) 2 (IntervalRat.scale (497 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45403583716 / 1000000000000) (45403583823 / 1000000000000), orderedInterval (1016053009 / 1000000000000) (1016053115 / 1000000000000)))) (orderedInterval (4050978876 / 1000000000000) (4050979051 / 1000000000000))) = true
  rfl'

theorem compactCertificate377_chunkChecks2 :
    compactCertificate377.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate377.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate377_chunkChecks2_0
    compactCertificate377_chunkChecks2_1 compactCertificate377_chunkChecks2_2

theorem compactCertificate377_chunkChecks3_0 :
    compactCertificate377.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (497 / 2) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45086923917 / 1000000000000) (-45086923916 / 1000000000000), orderedInterval (-22909639565 / 1000000000000) (-22909639564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (732175901106797 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (58913038875 / 1000000000000) (58913038991 / 1000000000000), orderedInterval (-2844528964 / 1000000000000) (-2844528848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (236770642914701 / 800000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45974090397 / 1000000000000) (45974090417 / 1000000000000), orderedInterval (6037001891 / 1000000000000) (6037001911 / 1000000000000)))) (orderedInterval (8437087898 / 1000000000000) (8437087928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (213647101870279 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77378404859 / 1000000000000) (-77378404858 / 1000000000000), orderedInterval (-76293043648 / 1000000000000) (-76293043647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (573886167574363 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16944034640 / 1000000000000) (-16944034427 / 1000000000000), orderedInterval (64480923273 / 1000000000000) (64480923486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1558212581722671 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28451573148 / 1000000000000) (28451573149 / 1000000000000), orderedInterval (28681748837 / 1000000000000) (28681748838 / 1000000000000)))) (orderedInterval (7372724317 / 1000000000000) (7372724390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1147772335149223 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45366548990 / 1000000000000) (-45366545436 / 1000000000000), orderedInterval (12747942537 / 1000000000000) (12747946091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1966727459430979 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24868600488 / 1000000000000) (24868610036 / 1000000000000), orderedInterval (-26031684500 / 1000000000000) (-26031674951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1448682545109961 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41709189629 / 1000000000000) (-41709188848 / 1000000000000), orderedInterval (4315688844 / 1000000000000) (4315689625 / 1000000000000)))) (orderedInterval (-6562901665 / 1000000000000) (-6562899242 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate377_chunkChecks3_1 :
    compactCertificate377.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2222651569634503 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12748529664 / 1000000000000) (-12748529663 / 1000000000000), orderedInterval (-31344063285 / 1000000000000) (-31344063284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1283248482043087 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40745202018 / 1000000000000) (40745202019 / 1000000000000), orderedInterval (17942815682 / 1000000000000) (17942815683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2277146950245083 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33170672211 / 1000000000000) (-33170672053 / 1000000000000), orderedInterval (-4211412209 / 1000000000000) (-4211412050 / 1000000000000)))) (orderedInterval (-57964352620 / 1000000000000) (-57964351387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2127606064652327 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33994519617 / 1000000000000) (-33994514268 / 1000000000000), orderedInterval (6454381825 / 1000000000000) (6454387173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1518360080261591 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9829123397 / 1000000000000) (-9829123396 / 1000000000000), orderedInterval (-39742735002 / 1000000000000) (-39742735001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1721658502723089 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27629925154 / 1000000000000) (-27629925153 / 1000000000000), orderedInterval (-26719951711 / 1000000000000) (-26719951710 / 1000000000000)))) (orderedInterval (13839168933 / 1000000000000) (13839170017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1435339367648641 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (41940465935 / 1000000000000) (41940465993 / 1000000000000), orderedInterval (3830768469 / 1000000000000) (3830768526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1268165860793461 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22483398088 / 1000000000000) (-22483398087 / 1000000000000), orderedInterval (-38726632450 / 1000000000000) (-38726632449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (367563895596639 / 800000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37223404860 / 1000000000000) (37223405250 / 1000000000000), orderedInterval (83377332 / 1000000000000) (83377722 / 1000000000000)))) (orderedInterval (-4723315814 / 1000000000000) (-4723315669 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate377_chunkChecks3_2 :
    compactCertificate377.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1016701079048333 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23604841000 / 1000000000000) (-23604840999 / 1000000000000), orderedInterval (-44083634251 / 1000000000000) (-44083634250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (861868764365413 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26908626623 / 1000000000000) (26908629802 / 1000000000000), orderedInterval (-47290948682 / 1000000000000) (-47290945503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (539317454890039 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34461288399 / 1000000000000) (-34461288398 / 1000000000000), orderedInterval (-59320551586 / 1000000000000) (-59320551585 / 1000000000000)))) (orderedInterval (-8968848168 / 1000000000000) (-8968847996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (290046720928713 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80745057701 / 1000000000000) (-80745057700 / 1000000000000), orderedInterval (-46979369879 / 1000000000000) (-46979369878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (787533269445139 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14192587594 / 1000000000000) (14192587733 / 1000000000000), orderedInterval (-55100252940 / 1000000000000) (-55100252802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1075309351137203 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26042742391 / 1000000000000) (-26042738451 / 1000000000000), orderedInterval (41156995413 / 1000000000000) (41156999353 / 1000000000000)))) (orderedInterval (3359099225 / 1000000000000) (3359099639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (454682545109961 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (73142220002 / 1000000000000) (73142220004 / 1000000000000), orderedInterval (15512771499 / 1000000000000) (15512771501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1848259302651881 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31932436875 / 1000000000000) (-31932436874 / 1000000000000), orderedInterval (-18888729008 / 1000000000000) (-18888729007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1234551558324679 / 4000000000000) 3 (IntervalRat.scale (497 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45403583716 / 1000000000000) (45403583823 / 1000000000000), orderedInterval (1016053009 / 1000000000000) (1016053115 / 1000000000000)))) (orderedInterval (-9544729535 / 1000000000000) (-9544729276 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate377_chunkChecks3 :
    compactCertificate377.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate377.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate377_chunkChecks3_0
    compactCertificate377_chunkChecks3_1 compactCertificate377_chunkChecks3_2

theorem compactCertificate377_chunkChecks4_0 :
    compactCertificate377.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (497 / 2) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45086923917 / 1000000000000) (-45086923916 / 1000000000000), orderedInterval (-22909639565 / 1000000000000) (-22909639564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (732175901106797 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (58913038875 / 1000000000000) (58913038991 / 1000000000000), orderedInterval (-2844528964 / 1000000000000) (-2844528848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (236770642914701 / 800000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45974090397 / 1000000000000) (45974090417 / 1000000000000), orderedInterval (6037001891 / 1000000000000) (6037001911 / 1000000000000)))) (orderedInterval (-12348732565 / 1000000000000) (-12348732530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (213647101870279 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77378404859 / 1000000000000) (-77378404858 / 1000000000000), orderedInterval (-76293043648 / 1000000000000) (-76293043647 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (573886167574363 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16944034640 / 1000000000000) (-16944034427 / 1000000000000), orderedInterval (64480923273 / 1000000000000) (64480923486 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1558212581722671 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28451573148 / 1000000000000) (28451573149 / 1000000000000), orderedInterval (28681748837 / 1000000000000) (28681748838 / 1000000000000)))) (orderedInterval (-12340651756 / 1000000000000) (-12340651646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1147772335149223 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45366548990 / 1000000000000) (-45366545436 / 1000000000000), orderedInterval (12747942537 / 1000000000000) (12747946091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1966727459430979 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24868600488 / 1000000000000) (24868610036 / 1000000000000), orderedInterval (-26031684500 / 1000000000000) (-26031674951 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1448682545109961 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41709189629 / 1000000000000) (-41709188848 / 1000000000000), orderedInterval (4315688844 / 1000000000000) (4315689625 / 1000000000000)))) (orderedInterval (-16250928501 / 1000000000000) (-16250923738 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate377_chunkChecks4_1 :
    compactCertificate377.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2222651569634503 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12748529664 / 1000000000000) (-12748529663 / 1000000000000), orderedInterval (-31344063285 / 1000000000000) (-31344063284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1283248482043087 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (40745202018 / 1000000000000) (40745202019 / 1000000000000), orderedInterval (17942815682 / 1000000000000) (17942815683 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2277146950245083 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33170672211 / 1000000000000) (-33170672053 / 1000000000000), orderedInterval (-4211412209 / 1000000000000) (-4211412050 / 1000000000000)))) (orderedInterval (-64394738096 / 1000000000000) (-64394735341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2127606064652327 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33994519617 / 1000000000000) (-33994514268 / 1000000000000), orderedInterval (6454381825 / 1000000000000) (6454387173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1518360080261591 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9829123397 / 1000000000000) (-9829123396 / 1000000000000), orderedInterval (-39742735002 / 1000000000000) (-39742735001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1721658502723089 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27629925154 / 1000000000000) (-27629925153 / 1000000000000), orderedInterval (-26719951711 / 1000000000000) (-26719951710 / 1000000000000)))) (orderedInterval (8968454949 / 1000000000000) (8968457219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1435339367648641 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (41940465935 / 1000000000000) (41940465993 / 1000000000000), orderedInterval (3830768469 / 1000000000000) (3830768526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1268165860793461 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22483398088 / 1000000000000) (-22483398087 / 1000000000000), orderedInterval (-38726632450 / 1000000000000) (-38726632449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (367563895596639 / 800000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37223404860 / 1000000000000) (37223405250 / 1000000000000), orderedInterval (83377332 / 1000000000000) (83377722 / 1000000000000)))) (orderedInterval (16690100003 / 1000000000000) (16690100249 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate377_chunkChecks4_2 :
    compactCertificate377.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1016701079048333 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23604841000 / 1000000000000) (-23604840999 / 1000000000000), orderedInterval (-44083634251 / 1000000000000) (-44083634250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (861868764365413 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26908626623 / 1000000000000) (26908629802 / 1000000000000), orderedInterval (-47290948682 / 1000000000000) (-47290945503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (539317454890039 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-34461288399 / 1000000000000) (-34461288398 / 1000000000000), orderedInterval (-59320551586 / 1000000000000) (-59320551585 / 1000000000000)))) (orderedInterval (3245081134 / 1000000000000) (3245081290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (290046720928713 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-80745057701 / 1000000000000) (-80745057700 / 1000000000000), orderedInterval (-46979369879 / 1000000000000) (-46979369878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (787533269445139 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14192587594 / 1000000000000) (14192587733 / 1000000000000), orderedInterval (-55100252940 / 1000000000000) (-55100252802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1075309351137203 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26042742391 / 1000000000000) (-26042738451 / 1000000000000), orderedInterval (41156995413 / 1000000000000) (41156999353 / 1000000000000)))) (orderedInterval (2590396090 / 1000000000000) (2590396537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (454682545109961 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (73142220002 / 1000000000000) (73142220004 / 1000000000000), orderedInterval (15512771499 / 1000000000000) (15512771501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1848259302651881 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31932436875 / 1000000000000) (-31932436874 / 1000000000000), orderedInterval (-18888729008 / 1000000000000) (-18888729007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1234551558324679 / 4000000000000) 4 (IntervalRat.scale (497 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45403583716 / 1000000000000) (45403583823 / 1000000000000), orderedInterval (1016053009 / 1000000000000) (1016053115 / 1000000000000)))) (orderedInterval (10897361360 / 1000000000000) (10897361763 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate377_chunkChecks4 :
    compactCertificate377.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate377.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate377_chunkChecks4_0
    compactCertificate377_chunkChecks4_1 compactCertificate377_chunkChecks4_2

theorem compactCertificate377_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate377.chunkCheck r b = true :=
  compactCertificate377.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate377_chunkChecks0
    · exact compactCertificate377_chunkChecks1
    · exact compactCertificate377_chunkChecks2
    · exact compactCertificate377_chunkChecks3
    · exact compactCertificate377_chunkChecks4)

theorem compactCertificate377_coefficient0 :
    compactCertificate377.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate377_coefficient1 :
    compactCertificate377.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate377_coefficient2 :
    compactCertificate377.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate377_coefficient3 :
    compactCertificate377.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate377_coefficient4 :
    compactCertificate377.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate377_coefficients : ∀ r : Fin 5,
    compactCertificate377.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate377_coefficient0
  · exact compactCertificate377_coefficient1
  · exact compactCertificate377_coefficient2
  · exact compactCertificate377_coefficient3
  · exact compactCertificate377_coefficient4

theorem compactCertificate377_lower : (1 : ℚ) ≤ compactCertificate377.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate377, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate377_proves {t : ℝ} (ht : t ∈ compactCertificate377.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate377.proves compactCertificate377_states compactCertificate377_chunks
    compactCertificate377_coefficients compactCertificate377_lower ht

end Erdos232
