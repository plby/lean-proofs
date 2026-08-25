/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate538 : CompactCertificate where
  left := 409
  right := 410
  center := 819 / 2
  grid := fun i =>
    match i.val with
    | 0 => 130
    | 1 => 96
    | 2 => 155
    | 3 => 28
    | 4 => 75
    | 5 => 204
    | 6 => 151
    | 7 => 258
    | 8 => 190
    | 9 => 292
    | 10 => 168
    | 11 => 299
    | 12 => 279
    | 13 => 199
    | 14 => 226
    | 15 => 188
    | 16 => 166
    | 17 => 241
    | 18 => 133
    | 19 => 113
    | 20 => 71
    | 21 => 38
    | 22 => 103
    | 23 => 141
    | 24 => 60
    | 25 => 242
    | _ => 162
  point := fun i =>
    match i.val with
    | 0 => 819 / 2
    | 1 => 1206543386330919 / 4000000000000
    | 2 => 390171341141127 / 800000000000
    | 3 => 352066350969333 / 4000000000000
    | 4 => 945699740932401 / 4000000000000
    | 5 => 2567758761430317 / 4000000000000
    | 6 => 1891399481865621 / 4000000000000
    | 7 => 3240945250048233 / 4000000000000
    | 8 => 2387265602505147 / 4000000000000
    | 9 => 3662679347144181 / 4000000000000
    | 10 => 2114648907028749 / 4000000000000
    | 11 => 3752481594065841 / 4000000000000
    | 12 => 3506055064286229 / 4000000000000
    | 13 => 2502086329445157 / 4000000000000
    | 14 => 2837099222797203 / 4000000000000
    | 15 => 2365277549505507 / 4000000000000
    | 16 => 2089794446659647 / 4000000000000
    | 17 => 605703884293053 / 800000000000
    | 18 => 1675408820403591 / 4000000000000
    | 19 => 1420262611700751 / 4000000000000
    | 20 => 888734397494853 / 4000000000000
    | 21 => 477964314769851 / 4000000000000
    | 22 => 1297766091902553 / 4000000000000
    | 23 => 1771988649057081 / 4000000000000
    | 24 => 749265602505147 / 4000000000000
    | 25 => 3045723076200987 / 4000000000000
    | _ => 2034401863718133 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (37582227704 / 1000000000000) (37582237433 / 1000000000000), orderedInterval (-11970735432 / 1000000000000) (-11970725703 / 1000000000000))
    | 1 => (orderedInterval (33837059137 / 1000000000000) (33837059138 / 1000000000000), orderedInterval (31018186380 / 1000000000000) (31018186381 / 1000000000000))
    | 2 => (orderedInterval (-36123034207 / 1000000000000) (-36123033820 / 1000000000000), orderedInterval (-625514490 / 1000000000000) (-625514103 / 1000000000000))
    | 3 => (orderedInterval (63099786816 / 1000000000000) (63099786817 / 1000000000000), orderedInterval (56662232176 / 1000000000000) (56662232177 / 1000000000000))
    | 4 => (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))
    | 5 => (orderedInterval (30357290226 / 1000000000000) (30357311309 / 1000000000000), orderedInterval (-8399021576 / 1000000000000) (-8399000493 / 1000000000000))
    | 6 => (orderedInterval (24889650192 / 1000000000000) (24889659003 / 1000000000000), orderedInterval (-26986509569 / 1000000000000) (-26986500758 / 1000000000000))
    | 7 => (orderedInterval (13208097055 / 1000000000000) (13208097056 / 1000000000000), orderedInterval (24715670992 / 1000000000000) (24715670993 / 1000000000000))
    | 8 => (orderedInterval (21014954459 / 1000000000000) (21014954460 / 1000000000000), orderedInterval (24983685667 / 1000000000000) (24983685668 / 1000000000000))
    | 9 => (orderedInterval (-20488794186 / 1000000000000) (-20488790350 / 1000000000000), orderedInterval (16608165047 / 1000000000000) (16608168883 / 1000000000000))
    | 10 => (orderedInterval (34564278218 / 1000000000000) (34564280029 / 1000000000000), orderedInterval (-3117979331 / 1000000000000) (-3117977520 / 1000000000000))
    | 11 => (orderedInterval (10872344403 / 1000000000000) (10872344410 / 1000000000000), orderedInterval (-23678652695 / 1000000000000) (-23678652687 / 1000000000000))
    | 12 => (orderedInterval (-19232502678 / 1000000000000) (-19232502677 / 1000000000000), orderedInterval (-18868111718 / 1000000000000) (-18868111717 / 1000000000000))
    | 13 => (orderedInterval (-28850477179 / 1000000000000) (-28850477177 / 1000000000000), orderedInterval (-13592814078 / 1000000000000) (-13592814075 / 1000000000000))
    | 14 => (orderedInterval (1799113261 / 1000000000000) (1799113262 / 1000000000000), orderedInterval (29904044833 / 1000000000000) (29904044834 / 1000000000000))
    | 15 => (orderedInterval (32691460958 / 1000000000000) (32691461277 / 1000000000000), orderedInterval (2778954132 / 1000000000000) (2778954451 / 1000000000000))
    | 16 => (orderedInterval (34469375520 / 1000000000000) (34469379293 / 1000000000000), orderedInterval (-5545918418 / 1000000000000) (-5545914646 / 1000000000000))
    | 17 => (orderedInterval (-20623874831 / 1000000000000) (-20623874830 / 1000000000000), orderedInterval (-20369922393 / 1000000000000) (-20369922392 / 1000000000000))
    | 18 => (orderedInterval (-37917370854 / 1000000000000) (-37917366005 / 1000000000000), orderedInterval (9110979545 / 1000000000000) (9110984395 / 1000000000000))
    | 19 => (orderedInterval (-31832120477 / 1000000000000) (-31832120476 / 1000000000000), orderedInterval (-27877914620 / 1000000000000) (-27877914619 / 1000000000000))
    | 20 => (orderedInterval (4525412886 / 1000000000000) (4525412896 / 1000000000000), orderedInterval (-53346988832 / 1000000000000) (-53346988822 / 1000000000000))
    | 21 => (orderedInterval (56944274614 / 1000000000000) (56944274615 / 1000000000000), orderedInterval (45424613517 / 1000000000000) (45424613518 / 1000000000000))
    | 22 => (orderedInterval (-44182920565 / 1000000000000) (-44182920140 / 1000000000000), orderedInterval (3241281321 / 1000000000000) (3241281746 / 1000000000000))
    | 23 => (orderedInterval (-27657633060 / 1000000000000) (-27657633059 / 1000000000000), orderedInterval (-25894242636 / 1000000000000) (-25894242635 / 1000000000000))
    | 24 => (orderedInterval (-22402634585 / 1000000000000) (-22402633672 / 1000000000000), orderedInterval (53881391243 / 1000000000000) (53881392156 / 1000000000000))
    | 25 => (orderedInterval (26854697988 / 1000000000000) (26854794341 / 1000000000000), orderedInterval (-10737103735 / 1000000000000) (-10737007382 / 1000000000000))
    | _ => (orderedInterval (15312626428 / 1000000000000) (15312626429 / 1000000000000), orderedInterval (31879034083 / 1000000000000) (31879034084 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13091834326 / 1000000000000) (13091838234 / 1000000000000)
      | 1 => orderedInterval (-4736950859 / 1000000000000) (-4736949307 / 1000000000000)
      | 2 => orderedInterval (100499416 / 1000000000000) (100499440 / 1000000000000)
      | 3 => orderedInterval (7747106986 / 1000000000000) (7747107965 / 1000000000000)
      | 4 => orderedInterval (-2390082357 / 1000000000000) (-2390082307 / 1000000000000)
      | 5 => orderedInterval (-2123110512 / 1000000000000) (-2123110253 / 1000000000000)
      | 6 => orderedInterval (8011722854 / 1000000000000) (8011723733 / 1000000000000)
      | 7 => orderedInterval (2070538839 / 1000000000000) (2070538898 / 1000000000000)
      | _ => orderedInterval (-5194133383 / 1000000000000) (-5194125420 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4575599494 / 1000000000000) (-4575595578 / 1000000000000)
      | 1 => orderedInterval (827572165 / 1000000000000) (827574574 / 1000000000000)
      | 2 => orderedInterval (-628341994 / 1000000000000) (-628341954 / 1000000000000)
      | 3 => orderedInterval (-14608317817 / 1000000000000) (-14608315781 / 1000000000000)
      | 4 => orderedInterval (-1496461644 / 1000000000000) (-1496461564 / 1000000000000)
      | 5 => orderedInterval (-513050061 / 1000000000000) (-513049723 / 1000000000000)
      | 6 => orderedInterval (-1064206038 / 1000000000000) (-1064205149 / 1000000000000)
      | 7 => orderedInterval (1843826659 / 1000000000000) (1843826711 / 1000000000000)
      | _ => orderedInterval (-5655131431 / 1000000000000) (-5655116685 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12049372539 / 1000000000000) (-12049368604 / 1000000000000)
      | 1 => orderedInterval (5964375723 / 1000000000000) (5964379491 / 1000000000000)
      | 2 => orderedInterval (517603064 / 1000000000000) (517603136 / 1000000000000)
      | 3 => orderedInterval (-30547027854 / 1000000000000) (-30547023492 / 1000000000000)
      | 4 => orderedInterval (4805998509 / 1000000000000) (4805998641 / 1000000000000)
      | 5 => orderedInterval (4230011482 / 1000000000000) (4230011927 / 1000000000000)
      | 6 => orderedInterval (-7738094269 / 1000000000000) (-7738093365 / 1000000000000)
      | 7 => orderedInterval (-3024789071 / 1000000000000) (-3024789021 / 1000000000000)
      | _ => orderedInterval (12031969494 / 1000000000000) (12031996884 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4720672564 / 1000000000000) (4720676512 / 1000000000000)
      | 1 => orderedInterval (-2316507367 / 1000000000000) (-2316501467 / 1000000000000)
      | 2 => orderedInterval (4034475420 / 1000000000000) (4034475550 / 1000000000000)
      | 3 => orderedInterval (74035795032 / 1000000000000) (74035804544 / 1000000000000)
      | 4 => orderedInterval (2015596646 / 1000000000000) (2015596870 / 1000000000000)
      | 5 => orderedInterval (2530404106 / 1000000000000) (2530404696 / 1000000000000)
      | 6 => orderedInterval (826587018 / 1000000000000) (826587938 / 1000000000000)
      | 7 => orderedInterval (-2447618607 / 1000000000000) (-2447618556 / 1000000000000)
      | _ => orderedInterval (5780164456 / 1000000000000) (5780215309 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10700875747 / 1000000000000) (10700879719 / 1000000000000)
      | 1 => orderedInterval (-13233181984 / 1000000000000) (-13233172725 / 1000000000000)
      | 2 => orderedInterval (-3971918134 / 1000000000000) (-3971917894 / 1000000000000)
      | 3 => orderedInterval (140337486906 / 1000000000000) (140337507893 / 1000000000000)
      | 4 => orderedInterval (-7657231527 / 1000000000000) (-7657231140 / 1000000000000)
      | 5 => orderedInterval (-9768061258 / 1000000000000) (-9768060461 / 1000000000000)
      | 6 => orderedInterval (7662849182 / 1000000000000) (7662850121 / 1000000000000)
      | 7 => orderedInterval (3302313244 / 1000000000000) (3302313296 / 1000000000000)
      | _ => orderedInterval (-33001941423 / 1000000000000) (-33001846836 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (16577425310 / 1000000000000) (16577440983 / 1000000000000)
    | 1 => orderedInterval (-25869709655 / 1000000000000) (-25869685149 / 1000000000000)
    | 2 => orderedInterval (-25809325461 / 1000000000000) (-25809284403 / 1000000000000)
    | 3 => orderedInterval (89179569268 / 1000000000000) (89179641396 / 1000000000000)
    | _ => orderedInterval (94371190753 / 1000000000000) (94371321973 / 1000000000000)

theorem compactCertificate538_stateChecks0 :
    compactCertificate538.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (819 / 2)) (orderedInterval (37582227704 / 1000000000000) (37582237433 / 1000000000000), orderedInterval (-11970735432 / 1000000000000) (-11970725703 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1206543386330919 / 4000000000000)) (orderedInterval (33837059137 / 1000000000000) (33837059138 / 1000000000000), orderedInterval (31018186380 / 1000000000000) (31018186381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (390171341141127 / 800000000000)) (orderedInterval (-36123034207 / 1000000000000) (-36123033820 / 1000000000000), orderedInterval (-625514490 / 1000000000000) (-625514103 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks1 :
    compactCertificate538.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (352066350969333 / 4000000000000)) (orderedInterval (63099786816 / 1000000000000) (63099786817 / 1000000000000), orderedInterval (56662232176 / 1000000000000) (56662232177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (945699740932401 / 4000000000000)) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2567758761430317 / 4000000000000)) (orderedInterval (30357290226 / 1000000000000) (30357311309 / 1000000000000), orderedInterval (-8399021576 / 1000000000000) (-8399000493 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks2 :
    compactCertificate538.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1891399481865621 / 4000000000000)) (orderedInterval (24889650192 / 1000000000000) (24889659003 / 1000000000000), orderedInterval (-26986509569 / 1000000000000) (-26986500758 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (3240945250048233 / 4000000000000)) (orderedInterval (13208097055 / 1000000000000) (13208097056 / 1000000000000), orderedInterval (24715670992 / 1000000000000) (24715670993 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2387265602505147 / 4000000000000)) (orderedInterval (21014954459 / 1000000000000) (21014954460 / 1000000000000), orderedInterval (24983685667 / 1000000000000) (24983685668 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks3 :
    compactCertificate538.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (3662679347144181 / 4000000000000)) (orderedInterval (-20488794186 / 1000000000000) (-20488790350 / 1000000000000), orderedInterval (16608165047 / 1000000000000) (16608168883 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2114648907028749 / 4000000000000)) (orderedInterval (34564278218 / 1000000000000) (34564280029 / 1000000000000), orderedInterval (-3117979331 / 1000000000000) (-3117977520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 299 12 (3752481594065841 / 4000000000000)) (orderedInterval (10872344403 / 1000000000000) (10872344410 / 1000000000000), orderedInterval (-23678652695 / 1000000000000) (-23678652687 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks4 :
    compactCertificate538.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (3506055064286229 / 4000000000000)) (orderedInterval (-19232502678 / 1000000000000) (-19232502677 / 1000000000000), orderedInterval (-18868111718 / 1000000000000) (-18868111717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2502086329445157 / 4000000000000)) (orderedInterval (-28850477179 / 1000000000000) (-28850477177 / 1000000000000), orderedInterval (-13592814078 / 1000000000000) (-13592814075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2837099222797203 / 4000000000000)) (orderedInterval (1799113261 / 1000000000000) (1799113262 / 1000000000000), orderedInterval (29904044833 / 1000000000000) (29904044834 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks5 :
    compactCertificate538.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2365277549505507 / 4000000000000)) (orderedInterval (32691460958 / 1000000000000) (32691461277 / 1000000000000), orderedInterval (2778954132 / 1000000000000) (2778954451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2089794446659647 / 4000000000000)) (orderedInterval (34469375520 / 1000000000000) (34469379293 / 1000000000000), orderedInterval (-5545918418 / 1000000000000) (-5545914646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (605703884293053 / 800000000000)) (orderedInterval (-20623874831 / 1000000000000) (-20623874830 / 1000000000000), orderedInterval (-20369922393 / 1000000000000) (-20369922392 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks6 :
    compactCertificate538.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1675408820403591 / 4000000000000)) (orderedInterval (-37917370854 / 1000000000000) (-37917366005 / 1000000000000), orderedInterval (9110979545 / 1000000000000) (9110984395 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1420262611700751 / 4000000000000)) (orderedInterval (-31832120477 / 1000000000000) (-31832120476 / 1000000000000), orderedInterval (-27877914620 / 1000000000000) (-27877914619 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (888734397494853 / 4000000000000)) (orderedInterval (4525412886 / 1000000000000) (4525412896 / 1000000000000), orderedInterval (-53346988832 / 1000000000000) (-53346988822 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks7 :
    compactCertificate538.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (477964314769851 / 4000000000000)) (orderedInterval (56944274614 / 1000000000000) (56944274615 / 1000000000000), orderedInterval (45424613517 / 1000000000000) (45424613518 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1297766091902553 / 4000000000000)) (orderedInterval (-44182920565 / 1000000000000) (-44182920140 / 1000000000000), orderedInterval (3241281321 / 1000000000000) (3241281746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1771988649057081 / 4000000000000)) (orderedInterval (-27657633060 / 1000000000000) (-27657633059 / 1000000000000), orderedInterval (-25894242636 / 1000000000000) (-25894242635 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_stateChecks8 :
    compactCertificate538.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (749265602505147 / 4000000000000)) (orderedInterval (-22402634585 / 1000000000000) (-22402633672 / 1000000000000), orderedInterval (53881391243 / 1000000000000) (53881392156 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3045723076200987 / 4000000000000)) (orderedInterval (26854697988 / 1000000000000) (26854794341 / 1000000000000), orderedInterval (-10737103735 / 1000000000000) (-10737007382 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2034401863718133 / 4000000000000)) (orderedInterval (15312626428 / 1000000000000) (15312626429 / 1000000000000), orderedInterval (31879034083 / 1000000000000) (31879034084 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_states : ∀ j,
    BesselStateValid (compactCertificate538.point j) (compactCertificate538.state j) :=
  compactCertificate538.statesValid_of_checks3 compactCertificate538_stateChecks0
    compactCertificate538_stateChecks1 compactCertificate538_stateChecks2
    compactCertificate538_stateChecks3 compactCertificate538_stateChecks4
    compactCertificate538_stateChecks5 compactCertificate538_stateChecks6
    compactCertificate538_stateChecks7 compactCertificate538_stateChecks8

theorem compactCertificate538_chunkChecks0_0 :
    compactCertificate538.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (819 / 2) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37582227704 / 1000000000000) (37582237433 / 1000000000000), orderedInterval (-11970735432 / 1000000000000) (-11970725703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1206543386330919 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33837059137 / 1000000000000) (33837059138 / 1000000000000), orderedInterval (31018186380 / 1000000000000) (31018186381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (390171341141127 / 800000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36123034207 / 1000000000000) (-36123033820 / 1000000000000), orderedInterval (-625514490 / 1000000000000) (-625514103 / 1000000000000)))) (orderedInterval (13091834326 / 1000000000000) (13091838234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (352066350969333 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (63099786816 / 1000000000000) (63099786817 / 1000000000000), orderedInterval (56662232176 / 1000000000000) (56662232177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2567758761430317 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30357290226 / 1000000000000) (30357311309 / 1000000000000), orderedInterval (-8399021576 / 1000000000000) (-8399000493 / 1000000000000)))) (orderedInterval (-4736950859 / 1000000000000) (-4736949307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1891399481865621 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24889650192 / 1000000000000) (24889659003 / 1000000000000), orderedInterval (-26986509569 / 1000000000000) (-26986500758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3240945250048233 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13208097055 / 1000000000000) (13208097056 / 1000000000000), orderedInterval (24715670992 / 1000000000000) (24715670993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2387265602505147 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21014954459 / 1000000000000) (21014954460 / 1000000000000), orderedInterval (24983685667 / 1000000000000) (24983685668 / 1000000000000)))) (orderedInterval (100499416 / 1000000000000) (100499440 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks0_1 :
    compactCertificate538.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3662679347144181 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20488794186 / 1000000000000) (-20488790350 / 1000000000000), orderedInterval (16608165047 / 1000000000000) (16608168883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2114648907028749 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34564278218 / 1000000000000) (34564280029 / 1000000000000), orderedInterval (-3117979331 / 1000000000000) (-3117977520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3752481594065841 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10872344403 / 1000000000000) (10872344410 / 1000000000000), orderedInterval (-23678652695 / 1000000000000) (-23678652687 / 1000000000000)))) (orderedInterval (7747106986 / 1000000000000) (7747107965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3506055064286229 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19232502678 / 1000000000000) (-19232502677 / 1000000000000), orderedInterval (-18868111718 / 1000000000000) (-18868111717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2502086329445157 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28850477179 / 1000000000000) (-28850477177 / 1000000000000), orderedInterval (-13592814078 / 1000000000000) (-13592814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2837099222797203 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1799113261 / 1000000000000) (1799113262 / 1000000000000), orderedInterval (29904044833 / 1000000000000) (29904044834 / 1000000000000)))) (orderedInterval (-2390082357 / 1000000000000) (-2390082307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2365277549505507 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32691460958 / 1000000000000) (32691461277 / 1000000000000), orderedInterval (2778954132 / 1000000000000) (2778954451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2089794446659647 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34469375520 / 1000000000000) (34469379293 / 1000000000000), orderedInterval (-5545918418 / 1000000000000) (-5545914646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (605703884293053 / 800000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20623874831 / 1000000000000) (-20623874830 / 1000000000000), orderedInterval (-20369922393 / 1000000000000) (-20369922392 / 1000000000000)))) (orderedInterval (-2123110512 / 1000000000000) (-2123110253 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks0_2 :
    compactCertificate538.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1675408820403591 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37917370854 / 1000000000000) (-37917366005 / 1000000000000), orderedInterval (9110979545 / 1000000000000) (9110984395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1420262611700751 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31832120477 / 1000000000000) (-31832120476 / 1000000000000), orderedInterval (-27877914620 / 1000000000000) (-27877914619 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (888734397494853 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4525412886 / 1000000000000) (4525412896 / 1000000000000), orderedInterval (-53346988832 / 1000000000000) (-53346988822 / 1000000000000)))) (orderedInterval (8011722854 / 1000000000000) (8011723733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (477964314769851 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56944274614 / 1000000000000) (56944274615 / 1000000000000), orderedInterval (45424613517 / 1000000000000) (45424613518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1297766091902553 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44182920565 / 1000000000000) (-44182920140 / 1000000000000), orderedInterval (3241281321 / 1000000000000) (3241281746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1771988649057081 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27657633060 / 1000000000000) (-27657633059 / 1000000000000), orderedInterval (-25894242636 / 1000000000000) (-25894242635 / 1000000000000)))) (orderedInterval (2070538839 / 1000000000000) (2070538898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (749265602505147 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22402634585 / 1000000000000) (-22402633672 / 1000000000000), orderedInterval (53881391243 / 1000000000000) (53881392156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3045723076200987 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26854697988 / 1000000000000) (26854794341 / 1000000000000), orderedInterval (-10737103735 / 1000000000000) (-10737007382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2034401863718133 / 4000000000000) 0 (IntervalRat.scale (819 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15312626428 / 1000000000000) (15312626429 / 1000000000000), orderedInterval (31879034083 / 1000000000000) (31879034084 / 1000000000000)))) (orderedInterval (-5194133383 / 1000000000000) (-5194125420 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks0 :
    compactCertificate538.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate538.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate538_chunkChecks0_0
    compactCertificate538_chunkChecks0_1 compactCertificate538_chunkChecks0_2

theorem compactCertificate538_chunkChecks1_0 :
    compactCertificate538.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (819 / 2) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37582227704 / 1000000000000) (37582237433 / 1000000000000), orderedInterval (-11970735432 / 1000000000000) (-11970725703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1206543386330919 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33837059137 / 1000000000000) (33837059138 / 1000000000000), orderedInterval (31018186380 / 1000000000000) (31018186381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (390171341141127 / 800000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36123034207 / 1000000000000) (-36123033820 / 1000000000000), orderedInterval (-625514490 / 1000000000000) (-625514103 / 1000000000000)))) (orderedInterval (-4575599494 / 1000000000000) (-4575595578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (352066350969333 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (63099786816 / 1000000000000) (63099786817 / 1000000000000), orderedInterval (56662232176 / 1000000000000) (56662232177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2567758761430317 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30357290226 / 1000000000000) (30357311309 / 1000000000000), orderedInterval (-8399021576 / 1000000000000) (-8399000493 / 1000000000000)))) (orderedInterval (827572165 / 1000000000000) (827574574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1891399481865621 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24889650192 / 1000000000000) (24889659003 / 1000000000000), orderedInterval (-26986509569 / 1000000000000) (-26986500758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3240945250048233 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13208097055 / 1000000000000) (13208097056 / 1000000000000), orderedInterval (24715670992 / 1000000000000) (24715670993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2387265602505147 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21014954459 / 1000000000000) (21014954460 / 1000000000000), orderedInterval (24983685667 / 1000000000000) (24983685668 / 1000000000000)))) (orderedInterval (-628341994 / 1000000000000) (-628341954 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks1_1 :
    compactCertificate538.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3662679347144181 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20488794186 / 1000000000000) (-20488790350 / 1000000000000), orderedInterval (16608165047 / 1000000000000) (16608168883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2114648907028749 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34564278218 / 1000000000000) (34564280029 / 1000000000000), orderedInterval (-3117979331 / 1000000000000) (-3117977520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3752481594065841 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10872344403 / 1000000000000) (10872344410 / 1000000000000), orderedInterval (-23678652695 / 1000000000000) (-23678652687 / 1000000000000)))) (orderedInterval (-14608317817 / 1000000000000) (-14608315781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3506055064286229 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19232502678 / 1000000000000) (-19232502677 / 1000000000000), orderedInterval (-18868111718 / 1000000000000) (-18868111717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2502086329445157 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28850477179 / 1000000000000) (-28850477177 / 1000000000000), orderedInterval (-13592814078 / 1000000000000) (-13592814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2837099222797203 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1799113261 / 1000000000000) (1799113262 / 1000000000000), orderedInterval (29904044833 / 1000000000000) (29904044834 / 1000000000000)))) (orderedInterval (-1496461644 / 1000000000000) (-1496461564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2365277549505507 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32691460958 / 1000000000000) (32691461277 / 1000000000000), orderedInterval (2778954132 / 1000000000000) (2778954451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2089794446659647 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34469375520 / 1000000000000) (34469379293 / 1000000000000), orderedInterval (-5545918418 / 1000000000000) (-5545914646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (605703884293053 / 800000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20623874831 / 1000000000000) (-20623874830 / 1000000000000), orderedInterval (-20369922393 / 1000000000000) (-20369922392 / 1000000000000)))) (orderedInterval (-513050061 / 1000000000000) (-513049723 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks1_2 :
    compactCertificate538.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1675408820403591 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37917370854 / 1000000000000) (-37917366005 / 1000000000000), orderedInterval (9110979545 / 1000000000000) (9110984395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1420262611700751 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31832120477 / 1000000000000) (-31832120476 / 1000000000000), orderedInterval (-27877914620 / 1000000000000) (-27877914619 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (888734397494853 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4525412886 / 1000000000000) (4525412896 / 1000000000000), orderedInterval (-53346988832 / 1000000000000) (-53346988822 / 1000000000000)))) (orderedInterval (-1064206038 / 1000000000000) (-1064205149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (477964314769851 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56944274614 / 1000000000000) (56944274615 / 1000000000000), orderedInterval (45424613517 / 1000000000000) (45424613518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1297766091902553 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44182920565 / 1000000000000) (-44182920140 / 1000000000000), orderedInterval (3241281321 / 1000000000000) (3241281746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1771988649057081 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27657633060 / 1000000000000) (-27657633059 / 1000000000000), orderedInterval (-25894242636 / 1000000000000) (-25894242635 / 1000000000000)))) (orderedInterval (1843826659 / 1000000000000) (1843826711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (749265602505147 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22402634585 / 1000000000000) (-22402633672 / 1000000000000), orderedInterval (53881391243 / 1000000000000) (53881392156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3045723076200987 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26854697988 / 1000000000000) (26854794341 / 1000000000000), orderedInterval (-10737103735 / 1000000000000) (-10737007382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2034401863718133 / 4000000000000) 1 (IntervalRat.scale (819 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15312626428 / 1000000000000) (15312626429 / 1000000000000), orderedInterval (31879034083 / 1000000000000) (31879034084 / 1000000000000)))) (orderedInterval (-5655131431 / 1000000000000) (-5655116685 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks1 :
    compactCertificate538.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate538.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate538_chunkChecks1_0
    compactCertificate538_chunkChecks1_1 compactCertificate538_chunkChecks1_2

theorem compactCertificate538_chunkChecks2_0 :
    compactCertificate538.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (819 / 2) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37582227704 / 1000000000000) (37582237433 / 1000000000000), orderedInterval (-11970735432 / 1000000000000) (-11970725703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1206543386330919 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33837059137 / 1000000000000) (33837059138 / 1000000000000), orderedInterval (31018186380 / 1000000000000) (31018186381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (390171341141127 / 800000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36123034207 / 1000000000000) (-36123033820 / 1000000000000), orderedInterval (-625514490 / 1000000000000) (-625514103 / 1000000000000)))) (orderedInterval (-12049372539 / 1000000000000) (-12049368604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (352066350969333 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (63099786816 / 1000000000000) (63099786817 / 1000000000000), orderedInterval (56662232176 / 1000000000000) (56662232177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2567758761430317 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30357290226 / 1000000000000) (30357311309 / 1000000000000), orderedInterval (-8399021576 / 1000000000000) (-8399000493 / 1000000000000)))) (orderedInterval (5964375723 / 1000000000000) (5964379491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1891399481865621 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24889650192 / 1000000000000) (24889659003 / 1000000000000), orderedInterval (-26986509569 / 1000000000000) (-26986500758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3240945250048233 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13208097055 / 1000000000000) (13208097056 / 1000000000000), orderedInterval (24715670992 / 1000000000000) (24715670993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2387265602505147 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21014954459 / 1000000000000) (21014954460 / 1000000000000), orderedInterval (24983685667 / 1000000000000) (24983685668 / 1000000000000)))) (orderedInterval (517603064 / 1000000000000) (517603136 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks2_1 :
    compactCertificate538.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3662679347144181 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20488794186 / 1000000000000) (-20488790350 / 1000000000000), orderedInterval (16608165047 / 1000000000000) (16608168883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2114648907028749 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34564278218 / 1000000000000) (34564280029 / 1000000000000), orderedInterval (-3117979331 / 1000000000000) (-3117977520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3752481594065841 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10872344403 / 1000000000000) (10872344410 / 1000000000000), orderedInterval (-23678652695 / 1000000000000) (-23678652687 / 1000000000000)))) (orderedInterval (-30547027854 / 1000000000000) (-30547023492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3506055064286229 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19232502678 / 1000000000000) (-19232502677 / 1000000000000), orderedInterval (-18868111718 / 1000000000000) (-18868111717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2502086329445157 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28850477179 / 1000000000000) (-28850477177 / 1000000000000), orderedInterval (-13592814078 / 1000000000000) (-13592814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2837099222797203 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1799113261 / 1000000000000) (1799113262 / 1000000000000), orderedInterval (29904044833 / 1000000000000) (29904044834 / 1000000000000)))) (orderedInterval (4805998509 / 1000000000000) (4805998641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2365277549505507 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32691460958 / 1000000000000) (32691461277 / 1000000000000), orderedInterval (2778954132 / 1000000000000) (2778954451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2089794446659647 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34469375520 / 1000000000000) (34469379293 / 1000000000000), orderedInterval (-5545918418 / 1000000000000) (-5545914646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (605703884293053 / 800000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20623874831 / 1000000000000) (-20623874830 / 1000000000000), orderedInterval (-20369922393 / 1000000000000) (-20369922392 / 1000000000000)))) (orderedInterval (4230011482 / 1000000000000) (4230011927 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks2_2 :
    compactCertificate538.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1675408820403591 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37917370854 / 1000000000000) (-37917366005 / 1000000000000), orderedInterval (9110979545 / 1000000000000) (9110984395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1420262611700751 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31832120477 / 1000000000000) (-31832120476 / 1000000000000), orderedInterval (-27877914620 / 1000000000000) (-27877914619 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (888734397494853 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4525412886 / 1000000000000) (4525412896 / 1000000000000), orderedInterval (-53346988832 / 1000000000000) (-53346988822 / 1000000000000)))) (orderedInterval (-7738094269 / 1000000000000) (-7738093365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (477964314769851 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56944274614 / 1000000000000) (56944274615 / 1000000000000), orderedInterval (45424613517 / 1000000000000) (45424613518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1297766091902553 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44182920565 / 1000000000000) (-44182920140 / 1000000000000), orderedInterval (3241281321 / 1000000000000) (3241281746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1771988649057081 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27657633060 / 1000000000000) (-27657633059 / 1000000000000), orderedInterval (-25894242636 / 1000000000000) (-25894242635 / 1000000000000)))) (orderedInterval (-3024789071 / 1000000000000) (-3024789021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (749265602505147 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22402634585 / 1000000000000) (-22402633672 / 1000000000000), orderedInterval (53881391243 / 1000000000000) (53881392156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3045723076200987 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26854697988 / 1000000000000) (26854794341 / 1000000000000), orderedInterval (-10737103735 / 1000000000000) (-10737007382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2034401863718133 / 4000000000000) 2 (IntervalRat.scale (819 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15312626428 / 1000000000000) (15312626429 / 1000000000000), orderedInterval (31879034083 / 1000000000000) (31879034084 / 1000000000000)))) (orderedInterval (12031969494 / 1000000000000) (12031996884 / 1000000000000))) = true
  rfl'

theorem compactCertificate538_chunkChecks2 :
    compactCertificate538.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate538.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate538_chunkChecks2_0
    compactCertificate538_chunkChecks2_1 compactCertificate538_chunkChecks2_2

theorem compactCertificate538_chunkChecks3_0 :
    compactCertificate538.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (819 / 2) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37582227704 / 1000000000000) (37582237433 / 1000000000000), orderedInterval (-11970735432 / 1000000000000) (-11970725703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1206543386330919 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33837059137 / 1000000000000) (33837059138 / 1000000000000), orderedInterval (31018186380 / 1000000000000) (31018186381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (390171341141127 / 800000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36123034207 / 1000000000000) (-36123033820 / 1000000000000), orderedInterval (-625514490 / 1000000000000) (-625514103 / 1000000000000)))) (orderedInterval (4720672564 / 1000000000000) (4720676512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (352066350969333 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (63099786816 / 1000000000000) (63099786817 / 1000000000000), orderedInterval (56662232176 / 1000000000000) (56662232177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2567758761430317 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30357290226 / 1000000000000) (30357311309 / 1000000000000), orderedInterval (-8399021576 / 1000000000000) (-8399000493 / 1000000000000)))) (orderedInterval (-2316507367 / 1000000000000) (-2316501467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1891399481865621 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24889650192 / 1000000000000) (24889659003 / 1000000000000), orderedInterval (-26986509569 / 1000000000000) (-26986500758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3240945250048233 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13208097055 / 1000000000000) (13208097056 / 1000000000000), orderedInterval (24715670992 / 1000000000000) (24715670993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2387265602505147 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21014954459 / 1000000000000) (21014954460 / 1000000000000), orderedInterval (24983685667 / 1000000000000) (24983685668 / 1000000000000)))) (orderedInterval (4034475420 / 1000000000000) (4034475550 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate538_chunkChecks3_1 :
    compactCertificate538.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3662679347144181 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20488794186 / 1000000000000) (-20488790350 / 1000000000000), orderedInterval (16608165047 / 1000000000000) (16608168883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2114648907028749 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34564278218 / 1000000000000) (34564280029 / 1000000000000), orderedInterval (-3117979331 / 1000000000000) (-3117977520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3752481594065841 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10872344403 / 1000000000000) (10872344410 / 1000000000000), orderedInterval (-23678652695 / 1000000000000) (-23678652687 / 1000000000000)))) (orderedInterval (74035795032 / 1000000000000) (74035804544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3506055064286229 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19232502678 / 1000000000000) (-19232502677 / 1000000000000), orderedInterval (-18868111718 / 1000000000000) (-18868111717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2502086329445157 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28850477179 / 1000000000000) (-28850477177 / 1000000000000), orderedInterval (-13592814078 / 1000000000000) (-13592814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2837099222797203 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1799113261 / 1000000000000) (1799113262 / 1000000000000), orderedInterval (29904044833 / 1000000000000) (29904044834 / 1000000000000)))) (orderedInterval (2015596646 / 1000000000000) (2015596870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2365277549505507 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32691460958 / 1000000000000) (32691461277 / 1000000000000), orderedInterval (2778954132 / 1000000000000) (2778954451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2089794446659647 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34469375520 / 1000000000000) (34469379293 / 1000000000000), orderedInterval (-5545918418 / 1000000000000) (-5545914646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (605703884293053 / 800000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20623874831 / 1000000000000) (-20623874830 / 1000000000000), orderedInterval (-20369922393 / 1000000000000) (-20369922392 / 1000000000000)))) (orderedInterval (2530404106 / 1000000000000) (2530404696 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate538_chunkChecks3_2 :
    compactCertificate538.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1675408820403591 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37917370854 / 1000000000000) (-37917366005 / 1000000000000), orderedInterval (9110979545 / 1000000000000) (9110984395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1420262611700751 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31832120477 / 1000000000000) (-31832120476 / 1000000000000), orderedInterval (-27877914620 / 1000000000000) (-27877914619 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (888734397494853 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4525412886 / 1000000000000) (4525412896 / 1000000000000), orderedInterval (-53346988832 / 1000000000000) (-53346988822 / 1000000000000)))) (orderedInterval (826587018 / 1000000000000) (826587938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (477964314769851 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56944274614 / 1000000000000) (56944274615 / 1000000000000), orderedInterval (45424613517 / 1000000000000) (45424613518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1297766091902553 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44182920565 / 1000000000000) (-44182920140 / 1000000000000), orderedInterval (3241281321 / 1000000000000) (3241281746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1771988649057081 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27657633060 / 1000000000000) (-27657633059 / 1000000000000), orderedInterval (-25894242636 / 1000000000000) (-25894242635 / 1000000000000)))) (orderedInterval (-2447618607 / 1000000000000) (-2447618556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (749265602505147 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22402634585 / 1000000000000) (-22402633672 / 1000000000000), orderedInterval (53881391243 / 1000000000000) (53881392156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3045723076200987 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26854697988 / 1000000000000) (26854794341 / 1000000000000), orderedInterval (-10737103735 / 1000000000000) (-10737007382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2034401863718133 / 4000000000000) 3 (IntervalRat.scale (819 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15312626428 / 1000000000000) (15312626429 / 1000000000000), orderedInterval (31879034083 / 1000000000000) (31879034084 / 1000000000000)))) (orderedInterval (5780164456 / 1000000000000) (5780215309 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate538_chunkChecks3 :
    compactCertificate538.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate538.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate538_chunkChecks3_0
    compactCertificate538_chunkChecks3_1 compactCertificate538_chunkChecks3_2

theorem compactCertificate538_chunkChecks4_0 :
    compactCertificate538.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (819 / 2) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37582227704 / 1000000000000) (37582237433 / 1000000000000), orderedInterval (-11970735432 / 1000000000000) (-11970725703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1206543386330919 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33837059137 / 1000000000000) (33837059138 / 1000000000000), orderedInterval (31018186380 / 1000000000000) (31018186381 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (390171341141127 / 800000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-36123034207 / 1000000000000) (-36123033820 / 1000000000000), orderedInterval (-625514490 / 1000000000000) (-625514103 / 1000000000000)))) (orderedInterval (10700875747 / 1000000000000) (10700879719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (352066350969333 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (63099786816 / 1000000000000) (63099786817 / 1000000000000), orderedInterval (56662232176 / 1000000000000) (56662232177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (945699740932401 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51881181538 / 1000000000000) (-51881181421 / 1000000000000), orderedInterval (1124613339 / 1000000000000) (1124613457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2567758761430317 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30357290226 / 1000000000000) (30357311309 / 1000000000000), orderedInterval (-8399021576 / 1000000000000) (-8399000493 / 1000000000000)))) (orderedInterval (-13233181984 / 1000000000000) (-13233172725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1891399481865621 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24889650192 / 1000000000000) (24889659003 / 1000000000000), orderedInterval (-26986509569 / 1000000000000) (-26986500758 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3240945250048233 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13208097055 / 1000000000000) (13208097056 / 1000000000000), orderedInterval (24715670992 / 1000000000000) (24715670993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2387265602505147 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21014954459 / 1000000000000) (21014954460 / 1000000000000), orderedInterval (24983685667 / 1000000000000) (24983685668 / 1000000000000)))) (orderedInterval (-3971918134 / 1000000000000) (-3971917894 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate538_chunkChecks4_1 :
    compactCertificate538.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3662679347144181 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20488794186 / 1000000000000) (-20488790350 / 1000000000000), orderedInterval (16608165047 / 1000000000000) (16608168883 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2114648907028749 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34564278218 / 1000000000000) (34564280029 / 1000000000000), orderedInterval (-3117979331 / 1000000000000) (-3117977520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3752481594065841 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10872344403 / 1000000000000) (10872344410 / 1000000000000), orderedInterval (-23678652695 / 1000000000000) (-23678652687 / 1000000000000)))) (orderedInterval (140337486906 / 1000000000000) (140337507893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3506055064286229 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-19232502678 / 1000000000000) (-19232502677 / 1000000000000), orderedInterval (-18868111718 / 1000000000000) (-18868111717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2502086329445157 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28850477179 / 1000000000000) (-28850477177 / 1000000000000), orderedInterval (-13592814078 / 1000000000000) (-13592814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2837099222797203 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1799113261 / 1000000000000) (1799113262 / 1000000000000), orderedInterval (29904044833 / 1000000000000) (29904044834 / 1000000000000)))) (orderedInterval (-7657231527 / 1000000000000) (-7657231140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2365277549505507 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32691460958 / 1000000000000) (32691461277 / 1000000000000), orderedInterval (2778954132 / 1000000000000) (2778954451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2089794446659647 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34469375520 / 1000000000000) (34469379293 / 1000000000000), orderedInterval (-5545918418 / 1000000000000) (-5545914646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (605703884293053 / 800000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20623874831 / 1000000000000) (-20623874830 / 1000000000000), orderedInterval (-20369922393 / 1000000000000) (-20369922392 / 1000000000000)))) (orderedInterval (-9768061258 / 1000000000000) (-9768060461 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate538_chunkChecks4_2 :
    compactCertificate538.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1675408820403591 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37917370854 / 1000000000000) (-37917366005 / 1000000000000), orderedInterval (9110979545 / 1000000000000) (9110984395 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1420262611700751 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31832120477 / 1000000000000) (-31832120476 / 1000000000000), orderedInterval (-27877914620 / 1000000000000) (-27877914619 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (888734397494853 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (4525412886 / 1000000000000) (4525412896 / 1000000000000), orderedInterval (-53346988832 / 1000000000000) (-53346988822 / 1000000000000)))) (orderedInterval (7662849182 / 1000000000000) (7662850121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (477964314769851 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56944274614 / 1000000000000) (56944274615 / 1000000000000), orderedInterval (45424613517 / 1000000000000) (45424613518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1297766091902553 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44182920565 / 1000000000000) (-44182920140 / 1000000000000), orderedInterval (3241281321 / 1000000000000) (3241281746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1771988649057081 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27657633060 / 1000000000000) (-27657633059 / 1000000000000), orderedInterval (-25894242636 / 1000000000000) (-25894242635 / 1000000000000)))) (orderedInterval (3302313244 / 1000000000000) (3302313296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (749265602505147 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-22402634585 / 1000000000000) (-22402633672 / 1000000000000), orderedInterval (53881391243 / 1000000000000) (53881392156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3045723076200987 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26854697988 / 1000000000000) (26854794341 / 1000000000000), orderedInterval (-10737103735 / 1000000000000) (-10737007382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2034401863718133 / 4000000000000) 4 (IntervalRat.scale (819 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15312626428 / 1000000000000) (15312626429 / 1000000000000), orderedInterval (31879034083 / 1000000000000) (31879034084 / 1000000000000)))) (orderedInterval (-33001941423 / 1000000000000) (-33001846836 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate538_chunkChecks4 :
    compactCertificate538.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate538.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate538_chunkChecks4_0
    compactCertificate538_chunkChecks4_1 compactCertificate538_chunkChecks4_2

theorem compactCertificate538_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate538.chunkCheck r b = true :=
  compactCertificate538.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate538_chunkChecks0
    · exact compactCertificate538_chunkChecks1
    · exact compactCertificate538_chunkChecks2
    · exact compactCertificate538_chunkChecks3
    · exact compactCertificate538_chunkChecks4)

theorem compactCertificate538_coefficient0 :
    compactCertificate538.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate538_coefficient1 :
    compactCertificate538.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate538_coefficient2 :
    compactCertificate538.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate538_coefficient3 :
    compactCertificate538.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate538_coefficient4 :
    compactCertificate538.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate538_coefficients : ∀ r : Fin 5,
    compactCertificate538.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate538_coefficient0
  · exact compactCertificate538_coefficient1
  · exact compactCertificate538_coefficient2
  · exact compactCertificate538_coefficient3
  · exact compactCertificate538_coefficient4

theorem compactCertificate538_lower : (1 : ℚ) ≤ compactCertificate538.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate538, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate538_proves {t : ℝ} (ht : t ∈ compactCertificate538.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate538.proves compactCertificate538_states compactCertificate538_chunks
    compactCertificate538_coefficients compactCertificate538_lower ht

end Erdos232
