/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate379 : CompactCertificate where
  left := 250
  right := 251
  center := 501 / 2
  grid := fun i =>
    match i.val with
    | 0 => 80
    | 1 => 59
    | 2 => 95
    | 3 => 17
    | 4 => 46
    | 5 => 125
    | 6 => 92
    | 7 => 158
    | 8 => 116
    | 9 => 178
    | 10 => 103
    | 11 => 183
    | 12 => 171
    | 13 => 122
    | 14 => 138
    | 15 => 115
    | 16 => 102
    | 17 => 148
    | 18 => 82
    | 19 => 69
    | 20 => 43
    | 21 => 23
    | 22 => 63
    | 23 => 86
    | 24 => 36
    | 25 => 148
    | _ => 99
  point := fun i =>
    match i.val with
    | 0 => 501 / 2
    | 1 => 738068664898401 / 4000000000000
    | 2 => 238676241650433 / 800000000000
    | 3 => 215366595647907 / 4000000000000
    | 4 => 578504969727879 / 4000000000000
    | 5 => 1570753528054443 / 4000000000000
    | 6 => 1157009939456259 / 4000000000000
    | 7 => 1982556251861007 / 4000000000000
    | 8 => 1460341961972013 / 4000000000000
    | 9 => 2240540113454499 / 4000000000000
    | 10 => 1293576437632971 / 4000000000000
    | 11 => 2295474088677639 / 4000000000000
    | 12 => 2144729654709891 / 4000000000000
    | 13 => 1530580282114803 / 4000000000000
    | 14 => 1735514909183637 / 4000000000000
    | 15 => 1446891394752453 / 4000000000000
    | 16 => 1278372427077513 / 4000000000000
    | 17 => 370522156325787 / 800000000000
    | 18 => 1024883783909889 / 4000000000000
    | 19 => 868805333897529 / 4000000000000
    | 20 => 543658038027987 / 4000000000000
    | 21 => 292381100976429 / 4000000000000
    | 22 => 793871565376287 / 4000000000000
    | 23 => 1083963752353599 / 4000000000000
    | 24 => 458341961972013 / 4000000000000
    | 25 => 1863134629031373 / 4000000000000
    | _ => 1244487586963107 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-2142535025 / 1000000000000) (-2142535021 / 1000000000000), orderedInterval (50371040188 / 1000000000000) (50371040193 / 1000000000000))
    | 1 => (orderedInterval (3057681432 / 1000000000000) (3057681440 / 1000000000000), orderedInterval (-58667094298 / 1000000000000) (-58667094290 / 1000000000000))
    | 2 => (orderedInterval (-29009420360 / 1000000000000) (-29009420359 / 1000000000000), orderedInterval (-35899812419 / 1000000000000) (-35899812418 / 1000000000000))
    | 3 => (orderedInterval (-102025413779 / 1000000000000) (-102025413778 / 1000000000000), orderedInterval (-36660536942 / 1000000000000) (-36660536941 / 1000000000000))
    | 4 => (orderedInterval (51867987151 / 1000000000000) (51867987152 / 1000000000000), orderedInterval (41191369692 / 1000000000000) (41191369693 / 1000000000000))
    | 5 => (orderedInterval (-28155464092 / 1000000000000) (-28155464091 / 1000000000000), orderedInterval (-28747009578 / 1000000000000) (-28747009577 / 1000000000000))
    | 6 => (orderedInterval (39751259366 / 1000000000000) (39751259367 / 1000000000000), orderedInterval (24846135409 / 1000000000000) (24846135410 / 1000000000000))
    | 7 => (orderedInterval (1883182122 / 1000000000000) (1883182123 / 1000000000000), orderedInterval (35787715555 / 1000000000000) (35787715556 / 1000000000000))
    | 8 => (orderedInterval (41432476131 / 1000000000000) (41432476168 / 1000000000000), orderedInterval (5149375293 / 1000000000000) (5149375330 / 1000000000000))
    | 9 => (orderedInterval (33354449599 / 1000000000000) (33354453640 / 1000000000000), orderedInterval (-4931519646 / 1000000000000) (-4931515605 / 1000000000000))
    | 10 => (orderedInterval (-24871731537 / 1000000000000) (-24871731536 / 1000000000000), orderedInterval (-36703278981 / 1000000000000) (-36703278980 / 1000000000000))
    | 11 => (orderedInterval (8490203962 / 1000000000000) (8490203971 / 1000000000000), orderedInterval (-32213989604 / 1000000000000) (-32213989595 / 1000000000000))
    | 12 => (orderedInterval (8350028824 / 1000000000000) (8350028834 / 1000000000000), orderedInterval (-33438264516 / 1000000000000) (-33438264506 / 1000000000000))
    | 13 => (orderedInterval (6330772287 / 1000000000000) (6330772288 / 1000000000000), orderedInterval (40286356165 / 1000000000000) (40286356166 / 1000000000000))
    | 14 => (orderedInterval (34545695108 / 1000000000000) (34545695109 / 1000000000000), orderedInterval (16509213125 / 1000000000000) (16509213126 / 1000000000000))
    | 15 => (orderedInterval (-39465003749 / 1000000000000) (-39465003747 / 1000000000000), orderedInterval (-14174917738 / 1000000000000) (-14174917737 / 1000000000000))
    | 16 => (orderedInterval (-2869467195 / 1000000000000) (-2869467191 / 1000000000000), orderedInterval (44543665657 / 1000000000000) (44543665660 / 1000000000000))
    | 17 => (orderedInterval (-31550686189 / 1000000000000) (-31550575590 / 1000000000000), orderedInterval (19504305189 / 1000000000000) (19504415787 / 1000000000000))
    | 18 => (orderedInterval (-28340042486 / 1000000000000) (-28340036068 / 1000000000000), orderedInterval (41061341366 / 1000000000000) (41061347784 / 1000000000000))
    | 19 => (orderedInterval (-50771788188 / 1000000000000) (-50771788187 / 1000000000000), orderedInterval (-18677587854 / 1000000000000) (-18677587853 / 1000000000000))
    | 20 => (orderedInterval (-68385372558 / 1000000000000) (-68385372482 / 1000000000000), orderedInterval (2968434841 / 1000000000000) (2968434917 / 1000000000000))
    | 21 => (orderedInterval (-93199447467 / 1000000000000) (-93199447409 / 1000000000000), orderedInterval (5444997487 / 1000000000000) (5444997545 / 1000000000000))
    | 22 => (orderedInterval (-55033391635 / 1000000000000) (-55033391633 / 1000000000000), orderedInterval (-13239999832 / 1000000000000) (-13239999830 / 1000000000000))
    | 23 => (orderedInterval (48449655698 / 1000000000000) (48449655866 / 1000000000000), orderedInterval (-1451696044 / 1000000000000) (-1451695876 / 1000000000000))
    | 24 => (orderedInterval (56929085529 / 1000000000000) (56929177705 / 1000000000000), orderedInterval (-48362012453 / 1000000000000) (-48361920277 / 1000000000000))
    | 25 => (orderedInterval (36936824655 / 1000000000000) (36936825372 / 1000000000000), orderedInterval (-1602197537 / 1000000000000) (-1602196820 / 1000000000000))
    | _ => (orderedInterval (-35128626017 / 1000000000000) (-35128626016 / 1000000000000), orderedInterval (-28442422398 / 1000000000000) (-28442422397 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-2523040088 / 1000000000000) (-2523040068 / 1000000000000)
      | 1 => orderedInterval (5002255995 / 1000000000000) (5002256026 / 1000000000000)
      | 2 => orderedInterval (943256323 / 1000000000000) (943256339 / 1000000000000)
      | 3 => orderedInterval (-6562541860 / 1000000000000) (-6562541041 / 1000000000000)
      | 4 => orderedInterval (273091052 / 1000000000000) (273091083 / 1000000000000)
      | 5 => orderedInterval (-1099340972 / 1000000000000) (-1099338115 / 1000000000000)
      | 6 => orderedInterval (5178734183 / 1000000000000) (5178735275 / 1000000000000)
      | 7 => orderedInterval (-743653231 / 1000000000000) (-743653186 / 1000000000000)
      | _ => orderedInterval (3927526041 / 1000000000000) (3927526725 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (17053638258 / 1000000000000) (17053638280 / 1000000000000)
      | 1 => orderedInterval (4157413514 / 1000000000000) (4157413549 / 1000000000000)
      | 2 => orderedInterval (-2002672384 / 1000000000000) (-2002672358 / 1000000000000)
      | 3 => orderedInterval (-12042275024 / 1000000000000) (-12042273209 / 1000000000000)
      | 4 => orderedInterval (6966655294 / 1000000000000) (6966655344 / 1000000000000)
      | 5 => orderedInterval (-2565218289 / 1000000000000) (-2565213018 / 1000000000000)
      | 6 => orderedInterval (-5746282349 / 1000000000000) (-5746281240 / 1000000000000)
      | 7 => orderedInterval (329001499 / 1000000000000) (329001540 / 1000000000000)
      | _ => orderedInterval (6737166661 / 1000000000000) (6737167122 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3180373980 / 1000000000000) (3180374005 / 1000000000000)
      | 1 => orderedInterval (-5617688882 / 1000000000000) (-5617688834 / 1000000000000)
      | 2 => orderedInterval (-1891554134 / 1000000000000) (-1891554087 / 1000000000000)
      | 3 => orderedInterval (26418597099 / 1000000000000) (26418601144 / 1000000000000)
      | 4 => orderedInterval (-209575812 / 1000000000000) (-209575730 / 1000000000000)
      | 5 => orderedInterval (3454727226 / 1000000000000) (3454736980 / 1000000000000)
      | 6 => orderedInterval (-6222835928 / 1000000000000) (-6222834794 / 1000000000000)
      | 7 => orderedInterval (3413868281 / 1000000000000) (3413868324 / 1000000000000)
      | _ => orderedInterval (129629043 / 1000000000000) (129629507 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16200286914 / 1000000000000) (-16200286885 / 1000000000000)
      | 1 => orderedInterval (-8143528414 / 1000000000000) (-8143528342 / 1000000000000)
      | 2 => orderedInterval (8172492567 / 1000000000000) (8172492650 / 1000000000000)
      | 3 => orderedInterval (51006947844 / 1000000000000) (51006956868 / 1000000000000)
      | 4 => orderedInterval (-19063019879 / 1000000000000) (-19063019740 / 1000000000000)
      | 5 => orderedInterval (2616271939 / 1000000000000) (2616289956 / 1000000000000)
      | 6 => orderedInterval (6345757759 / 1000000000000) (6345758916 / 1000000000000)
      | 7 => orderedInterval (-301363941 / 1000000000000) (-301363896 / 1000000000000)
      | _ => orderedInterval (-11035161403 / 1000000000000) (-11035160751 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4136625853 / 1000000000000) (-4136625820 / 1000000000000)
      | 1 => orderedInterval (12365039754 / 1000000000000) (12365039864 / 1000000000000)
      | 2 => orderedInterval (3562332441 / 1000000000000) (3562332593 / 1000000000000)
      | 3 => orderedInterval (-120449662937 / 1000000000000) (-120449642740 / 1000000000000)
      | 4 => orderedInterval (-1326007415 / 1000000000000) (-1326007175 / 1000000000000)
      | 5 => orderedInterval (-11007406614 / 1000000000000) (-11007373252 / 1000000000000)
      | 6 => orderedInterval (6340272429 / 1000000000000) (6340273615 / 1000000000000)
      | 7 => orderedInterval (-4578534971 / 1000000000000) (-4578534923 / 1000000000000)
      | _ => orderedInterval (-20155005575 / 1000000000000) (-20155004492 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4396287443 / 1000000000000) (4396293038 / 1000000000000)
    | 1 => orderedInterval (12887427180 / 1000000000000) (12887436010 / 1000000000000)
    | 2 => orderedInterval (22655540873 / 1000000000000) (22655556515 / 1000000000000)
    | 3 => orderedInterval (13398109558 / 1000000000000) (13398138776 / 1000000000000)
    | _ => orderedInterval (-139385598741 / 1000000000000) (-139385542330 / 1000000000000)

theorem compactCertificate379_stateChecks0 :
    compactCertificate379.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (501 / 2)) (orderedInterval (-2142535025 / 1000000000000) (-2142535021 / 1000000000000), orderedInterval (50371040188 / 1000000000000) (50371040193 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (738068664898401 / 4000000000000)) (orderedInterval (3057681432 / 1000000000000) (3057681440 / 1000000000000), orderedInterval (-58667094298 / 1000000000000) (-58667094290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (238676241650433 / 800000000000)) (orderedInterval (-29009420360 / 1000000000000) (-29009420359 / 1000000000000), orderedInterval (-35899812419 / 1000000000000) (-35899812418 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks1 :
    compactCertificate379.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (215366595647907 / 4000000000000)) (orderedInterval (-102025413779 / 1000000000000) (-102025413778 / 1000000000000), orderedInterval (-36660536942 / 1000000000000) (-36660536941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (578504969727879 / 4000000000000)) (orderedInterval (51867987151 / 1000000000000) (51867987152 / 1000000000000), orderedInterval (41191369692 / 1000000000000) (41191369693 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1570753528054443 / 4000000000000)) (orderedInterval (-28155464092 / 1000000000000) (-28155464091 / 1000000000000), orderedInterval (-28747009578 / 1000000000000) (-28747009577 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks2 :
    compactCertificate379.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1157009939456259 / 4000000000000)) (orderedInterval (39751259366 / 1000000000000) (39751259367 / 1000000000000), orderedInterval (24846135409 / 1000000000000) (24846135410 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1982556251861007 / 4000000000000)) (orderedInterval (1883182122 / 1000000000000) (1883182123 / 1000000000000), orderedInterval (35787715555 / 1000000000000) (35787715556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1460341961972013 / 4000000000000)) (orderedInterval (41432476131 / 1000000000000) (41432476168 / 1000000000000), orderedInterval (5149375293 / 1000000000000) (5149375330 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks3 :
    compactCertificate379.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2240540113454499 / 4000000000000)) (orderedInterval (33354449599 / 1000000000000) (33354453640 / 1000000000000), orderedInterval (-4931519646 / 1000000000000) (-4931515605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1293576437632971 / 4000000000000)) (orderedInterval (-24871731537 / 1000000000000) (-24871731536 / 1000000000000), orderedInterval (-36703278981 / 1000000000000) (-36703278980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2295474088677639 / 4000000000000)) (orderedInterval (8490203962 / 1000000000000) (8490203971 / 1000000000000), orderedInterval (-32213989604 / 1000000000000) (-32213989595 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks4 :
    compactCertificate379.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2144729654709891 / 4000000000000)) (orderedInterval (8350028824 / 1000000000000) (8350028834 / 1000000000000), orderedInterval (-33438264516 / 1000000000000) (-33438264506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1530580282114803 / 4000000000000)) (orderedInterval (6330772287 / 1000000000000) (6330772288 / 1000000000000), orderedInterval (40286356165 / 1000000000000) (40286356166 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1735514909183637 / 4000000000000)) (orderedInterval (34545695108 / 1000000000000) (34545695109 / 1000000000000), orderedInterval (16509213125 / 1000000000000) (16509213126 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks5 :
    compactCertificate379.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1446891394752453 / 4000000000000)) (orderedInterval (-39465003749 / 1000000000000) (-39465003747 / 1000000000000), orderedInterval (-14174917738 / 1000000000000) (-14174917737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1278372427077513 / 4000000000000)) (orderedInterval (-2869467195 / 1000000000000) (-2869467191 / 1000000000000), orderedInterval (44543665657 / 1000000000000) (44543665660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (370522156325787 / 800000000000)) (orderedInterval (-31550686189 / 1000000000000) (-31550575590 / 1000000000000), orderedInterval (19504305189 / 1000000000000) (19504415787 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks6 :
    compactCertificate379.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1024883783909889 / 4000000000000)) (orderedInterval (-28340042486 / 1000000000000) (-28340036068 / 1000000000000), orderedInterval (41061341366 / 1000000000000) (41061347784 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (868805333897529 / 4000000000000)) (orderedInterval (-50771788188 / 1000000000000) (-50771788187 / 1000000000000), orderedInterval (-18677587854 / 1000000000000) (-18677587853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543658038027987 / 4000000000000)) (orderedInterval (-68385372558 / 1000000000000) (-68385372482 / 1000000000000), orderedInterval (2968434841 / 1000000000000) (2968434917 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks7 :
    compactCertificate379.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (292381100976429 / 4000000000000)) (orderedInterval (-93199447467 / 1000000000000) (-93199447409 / 1000000000000), orderedInterval (5444997487 / 1000000000000) (5444997545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (793871565376287 / 4000000000000)) (orderedInterval (-55033391635 / 1000000000000) (-55033391633 / 1000000000000), orderedInterval (-13239999832 / 1000000000000) (-13239999830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1083963752353599 / 4000000000000)) (orderedInterval (48449655698 / 1000000000000) (48449655866 / 1000000000000), orderedInterval (-1451696044 / 1000000000000) (-1451695876 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_stateChecks8 :
    compactCertificate379.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (458341961972013 / 4000000000000)) (orderedInterval (56929085529 / 1000000000000) (56929177705 / 1000000000000), orderedInterval (-48362012453 / 1000000000000) (-48361920277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1863134629031373 / 4000000000000)) (orderedInterval (36936824655 / 1000000000000) (36936825372 / 1000000000000), orderedInterval (-1602197537 / 1000000000000) (-1602196820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1244487586963107 / 4000000000000)) (orderedInterval (-35128626017 / 1000000000000) (-35128626016 / 1000000000000), orderedInterval (-28442422398 / 1000000000000) (-28442422397 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_states : ∀ j,
    BesselStateValid (compactCertificate379.point j) (compactCertificate379.state j) :=
  compactCertificate379.statesValid_of_checks3 compactCertificate379_stateChecks0
    compactCertificate379_stateChecks1 compactCertificate379_stateChecks2
    compactCertificate379_stateChecks3 compactCertificate379_stateChecks4
    compactCertificate379_stateChecks5 compactCertificate379_stateChecks6
    compactCertificate379_stateChecks7 compactCertificate379_stateChecks8

theorem compactCertificate379_chunkChecks0_0 :
    compactCertificate379.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (501 / 2) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-2142535025 / 1000000000000) (-2142535021 / 1000000000000), orderedInterval (50371040188 / 1000000000000) (50371040193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (738068664898401 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3057681432 / 1000000000000) (3057681440 / 1000000000000), orderedInterval (-58667094298 / 1000000000000) (-58667094290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (238676241650433 / 800000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29009420360 / 1000000000000) (-29009420359 / 1000000000000), orderedInterval (-35899812419 / 1000000000000) (-35899812418 / 1000000000000)))) (orderedInterval (-2523040088 / 1000000000000) (-2523040068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (215366595647907 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102025413779 / 1000000000000) (-102025413778 / 1000000000000), orderedInterval (-36660536942 / 1000000000000) (-36660536941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (578504969727879 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51867987151 / 1000000000000) (51867987152 / 1000000000000), orderedInterval (41191369692 / 1000000000000) (41191369693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1570753528054443 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28155464092 / 1000000000000) (-28155464091 / 1000000000000), orderedInterval (-28747009578 / 1000000000000) (-28747009577 / 1000000000000)))) (orderedInterval (5002255995 / 1000000000000) (5002256026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1157009939456259 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39751259366 / 1000000000000) (39751259367 / 1000000000000), orderedInterval (24846135409 / 1000000000000) (24846135410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1982556251861007 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1883182122 / 1000000000000) (1883182123 / 1000000000000), orderedInterval (35787715555 / 1000000000000) (35787715556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1460341961972013 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41432476131 / 1000000000000) (41432476168 / 1000000000000), orderedInterval (5149375293 / 1000000000000) (5149375330 / 1000000000000)))) (orderedInterval (943256323 / 1000000000000) (943256339 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks0_1 :
    compactCertificate379.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2240540113454499 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33354449599 / 1000000000000) (33354453640 / 1000000000000), orderedInterval (-4931519646 / 1000000000000) (-4931515605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1293576437632971 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24871731537 / 1000000000000) (-24871731536 / 1000000000000), orderedInterval (-36703278981 / 1000000000000) (-36703278980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2295474088677639 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8490203962 / 1000000000000) (8490203971 / 1000000000000), orderedInterval (-32213989604 / 1000000000000) (-32213989595 / 1000000000000)))) (orderedInterval (-6562541860 / 1000000000000) (-6562541041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2144729654709891 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8350028824 / 1000000000000) (8350028834 / 1000000000000), orderedInterval (-33438264516 / 1000000000000) (-33438264506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1530580282114803 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6330772287 / 1000000000000) (6330772288 / 1000000000000), orderedInterval (40286356165 / 1000000000000) (40286356166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1735514909183637 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34545695108 / 1000000000000) (34545695109 / 1000000000000), orderedInterval (16509213125 / 1000000000000) (16509213126 / 1000000000000)))) (orderedInterval (273091052 / 1000000000000) (273091083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1446891394752453 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39465003749 / 1000000000000) (-39465003747 / 1000000000000), orderedInterval (-14174917738 / 1000000000000) (-14174917737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1278372427077513 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2869467195 / 1000000000000) (-2869467191 / 1000000000000), orderedInterval (44543665657 / 1000000000000) (44543665660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (370522156325787 / 800000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31550686189 / 1000000000000) (-31550575590 / 1000000000000), orderedInterval (19504305189 / 1000000000000) (19504415787 / 1000000000000)))) (orderedInterval (-1099340972 / 1000000000000) (-1099338115 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks0_2 :
    compactCertificate379.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1024883783909889 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28340042486 / 1000000000000) (-28340036068 / 1000000000000), orderedInterval (41061341366 / 1000000000000) (41061347784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (868805333897529 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50771788188 / 1000000000000) (-50771788187 / 1000000000000), orderedInterval (-18677587854 / 1000000000000) (-18677587853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (543658038027987 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68385372558 / 1000000000000) (-68385372482 / 1000000000000), orderedInterval (2968434841 / 1000000000000) (2968434917 / 1000000000000)))) (orderedInterval (5178734183 / 1000000000000) (5178735275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (292381100976429 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93199447467 / 1000000000000) (-93199447409 / 1000000000000), orderedInterval (5444997487 / 1000000000000) (5444997545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (793871565376287 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55033391635 / 1000000000000) (-55033391633 / 1000000000000), orderedInterval (-13239999832 / 1000000000000) (-13239999830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1083963752353599 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48449655698 / 1000000000000) (48449655866 / 1000000000000), orderedInterval (-1451696044 / 1000000000000) (-1451695876 / 1000000000000)))) (orderedInterval (-743653231 / 1000000000000) (-743653186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (458341961972013 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56929085529 / 1000000000000) (56929177705 / 1000000000000), orderedInterval (-48362012453 / 1000000000000) (-48361920277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1863134629031373 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36936824655 / 1000000000000) (36936825372 / 1000000000000), orderedInterval (-1602197537 / 1000000000000) (-1602196820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1244487586963107 / 4000000000000) 0 (IntervalRat.scale (501 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35128626017 / 1000000000000) (-35128626016 / 1000000000000), orderedInterval (-28442422398 / 1000000000000) (-28442422397 / 1000000000000)))) (orderedInterval (3927526041 / 1000000000000) (3927526725 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks0 :
    compactCertificate379.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate379.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate379_chunkChecks0_0
    compactCertificate379_chunkChecks0_1 compactCertificate379_chunkChecks0_2

theorem compactCertificate379_chunkChecks1_0 :
    compactCertificate379.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (501 / 2) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-2142535025 / 1000000000000) (-2142535021 / 1000000000000), orderedInterval (50371040188 / 1000000000000) (50371040193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (738068664898401 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3057681432 / 1000000000000) (3057681440 / 1000000000000), orderedInterval (-58667094298 / 1000000000000) (-58667094290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (238676241650433 / 800000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29009420360 / 1000000000000) (-29009420359 / 1000000000000), orderedInterval (-35899812419 / 1000000000000) (-35899812418 / 1000000000000)))) (orderedInterval (17053638258 / 1000000000000) (17053638280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (215366595647907 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102025413779 / 1000000000000) (-102025413778 / 1000000000000), orderedInterval (-36660536942 / 1000000000000) (-36660536941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (578504969727879 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51867987151 / 1000000000000) (51867987152 / 1000000000000), orderedInterval (41191369692 / 1000000000000) (41191369693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1570753528054443 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28155464092 / 1000000000000) (-28155464091 / 1000000000000), orderedInterval (-28747009578 / 1000000000000) (-28747009577 / 1000000000000)))) (orderedInterval (4157413514 / 1000000000000) (4157413549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1157009939456259 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39751259366 / 1000000000000) (39751259367 / 1000000000000), orderedInterval (24846135409 / 1000000000000) (24846135410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1982556251861007 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1883182122 / 1000000000000) (1883182123 / 1000000000000), orderedInterval (35787715555 / 1000000000000) (35787715556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1460341961972013 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41432476131 / 1000000000000) (41432476168 / 1000000000000), orderedInterval (5149375293 / 1000000000000) (5149375330 / 1000000000000)))) (orderedInterval (-2002672384 / 1000000000000) (-2002672358 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks1_1 :
    compactCertificate379.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2240540113454499 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33354449599 / 1000000000000) (33354453640 / 1000000000000), orderedInterval (-4931519646 / 1000000000000) (-4931515605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1293576437632971 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24871731537 / 1000000000000) (-24871731536 / 1000000000000), orderedInterval (-36703278981 / 1000000000000) (-36703278980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2295474088677639 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8490203962 / 1000000000000) (8490203971 / 1000000000000), orderedInterval (-32213989604 / 1000000000000) (-32213989595 / 1000000000000)))) (orderedInterval (-12042275024 / 1000000000000) (-12042273209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2144729654709891 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8350028824 / 1000000000000) (8350028834 / 1000000000000), orderedInterval (-33438264516 / 1000000000000) (-33438264506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1530580282114803 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6330772287 / 1000000000000) (6330772288 / 1000000000000), orderedInterval (40286356165 / 1000000000000) (40286356166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1735514909183637 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34545695108 / 1000000000000) (34545695109 / 1000000000000), orderedInterval (16509213125 / 1000000000000) (16509213126 / 1000000000000)))) (orderedInterval (6966655294 / 1000000000000) (6966655344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1446891394752453 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39465003749 / 1000000000000) (-39465003747 / 1000000000000), orderedInterval (-14174917738 / 1000000000000) (-14174917737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1278372427077513 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2869467195 / 1000000000000) (-2869467191 / 1000000000000), orderedInterval (44543665657 / 1000000000000) (44543665660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (370522156325787 / 800000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31550686189 / 1000000000000) (-31550575590 / 1000000000000), orderedInterval (19504305189 / 1000000000000) (19504415787 / 1000000000000)))) (orderedInterval (-2565218289 / 1000000000000) (-2565213018 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks1_2 :
    compactCertificate379.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1024883783909889 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28340042486 / 1000000000000) (-28340036068 / 1000000000000), orderedInterval (41061341366 / 1000000000000) (41061347784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (868805333897529 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50771788188 / 1000000000000) (-50771788187 / 1000000000000), orderedInterval (-18677587854 / 1000000000000) (-18677587853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (543658038027987 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68385372558 / 1000000000000) (-68385372482 / 1000000000000), orderedInterval (2968434841 / 1000000000000) (2968434917 / 1000000000000)))) (orderedInterval (-5746282349 / 1000000000000) (-5746281240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (292381100976429 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93199447467 / 1000000000000) (-93199447409 / 1000000000000), orderedInterval (5444997487 / 1000000000000) (5444997545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (793871565376287 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55033391635 / 1000000000000) (-55033391633 / 1000000000000), orderedInterval (-13239999832 / 1000000000000) (-13239999830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1083963752353599 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48449655698 / 1000000000000) (48449655866 / 1000000000000), orderedInterval (-1451696044 / 1000000000000) (-1451695876 / 1000000000000)))) (orderedInterval (329001499 / 1000000000000) (329001540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (458341961972013 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56929085529 / 1000000000000) (56929177705 / 1000000000000), orderedInterval (-48362012453 / 1000000000000) (-48361920277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1863134629031373 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36936824655 / 1000000000000) (36936825372 / 1000000000000), orderedInterval (-1602197537 / 1000000000000) (-1602196820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1244487586963107 / 4000000000000) 1 (IntervalRat.scale (501 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35128626017 / 1000000000000) (-35128626016 / 1000000000000), orderedInterval (-28442422398 / 1000000000000) (-28442422397 / 1000000000000)))) (orderedInterval (6737166661 / 1000000000000) (6737167122 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks1 :
    compactCertificate379.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate379.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate379_chunkChecks1_0
    compactCertificate379_chunkChecks1_1 compactCertificate379_chunkChecks1_2

theorem compactCertificate379_chunkChecks2_0 :
    compactCertificate379.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (501 / 2) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-2142535025 / 1000000000000) (-2142535021 / 1000000000000), orderedInterval (50371040188 / 1000000000000) (50371040193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (738068664898401 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3057681432 / 1000000000000) (3057681440 / 1000000000000), orderedInterval (-58667094298 / 1000000000000) (-58667094290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (238676241650433 / 800000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29009420360 / 1000000000000) (-29009420359 / 1000000000000), orderedInterval (-35899812419 / 1000000000000) (-35899812418 / 1000000000000)))) (orderedInterval (3180373980 / 1000000000000) (3180374005 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (215366595647907 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102025413779 / 1000000000000) (-102025413778 / 1000000000000), orderedInterval (-36660536942 / 1000000000000) (-36660536941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (578504969727879 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51867987151 / 1000000000000) (51867987152 / 1000000000000), orderedInterval (41191369692 / 1000000000000) (41191369693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1570753528054443 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28155464092 / 1000000000000) (-28155464091 / 1000000000000), orderedInterval (-28747009578 / 1000000000000) (-28747009577 / 1000000000000)))) (orderedInterval (-5617688882 / 1000000000000) (-5617688834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1157009939456259 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39751259366 / 1000000000000) (39751259367 / 1000000000000), orderedInterval (24846135409 / 1000000000000) (24846135410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1982556251861007 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1883182122 / 1000000000000) (1883182123 / 1000000000000), orderedInterval (35787715555 / 1000000000000) (35787715556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1460341961972013 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41432476131 / 1000000000000) (41432476168 / 1000000000000), orderedInterval (5149375293 / 1000000000000) (5149375330 / 1000000000000)))) (orderedInterval (-1891554134 / 1000000000000) (-1891554087 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks2_1 :
    compactCertificate379.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2240540113454499 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33354449599 / 1000000000000) (33354453640 / 1000000000000), orderedInterval (-4931519646 / 1000000000000) (-4931515605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1293576437632971 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24871731537 / 1000000000000) (-24871731536 / 1000000000000), orderedInterval (-36703278981 / 1000000000000) (-36703278980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2295474088677639 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8490203962 / 1000000000000) (8490203971 / 1000000000000), orderedInterval (-32213989604 / 1000000000000) (-32213989595 / 1000000000000)))) (orderedInterval (26418597099 / 1000000000000) (26418601144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2144729654709891 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8350028824 / 1000000000000) (8350028834 / 1000000000000), orderedInterval (-33438264516 / 1000000000000) (-33438264506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1530580282114803 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6330772287 / 1000000000000) (6330772288 / 1000000000000), orderedInterval (40286356165 / 1000000000000) (40286356166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1735514909183637 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34545695108 / 1000000000000) (34545695109 / 1000000000000), orderedInterval (16509213125 / 1000000000000) (16509213126 / 1000000000000)))) (orderedInterval (-209575812 / 1000000000000) (-209575730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1446891394752453 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39465003749 / 1000000000000) (-39465003747 / 1000000000000), orderedInterval (-14174917738 / 1000000000000) (-14174917737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1278372427077513 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2869467195 / 1000000000000) (-2869467191 / 1000000000000), orderedInterval (44543665657 / 1000000000000) (44543665660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (370522156325787 / 800000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31550686189 / 1000000000000) (-31550575590 / 1000000000000), orderedInterval (19504305189 / 1000000000000) (19504415787 / 1000000000000)))) (orderedInterval (3454727226 / 1000000000000) (3454736980 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks2_2 :
    compactCertificate379.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1024883783909889 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28340042486 / 1000000000000) (-28340036068 / 1000000000000), orderedInterval (41061341366 / 1000000000000) (41061347784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (868805333897529 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50771788188 / 1000000000000) (-50771788187 / 1000000000000), orderedInterval (-18677587854 / 1000000000000) (-18677587853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (543658038027987 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68385372558 / 1000000000000) (-68385372482 / 1000000000000), orderedInterval (2968434841 / 1000000000000) (2968434917 / 1000000000000)))) (orderedInterval (-6222835928 / 1000000000000) (-6222834794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (292381100976429 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93199447467 / 1000000000000) (-93199447409 / 1000000000000), orderedInterval (5444997487 / 1000000000000) (5444997545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (793871565376287 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55033391635 / 1000000000000) (-55033391633 / 1000000000000), orderedInterval (-13239999832 / 1000000000000) (-13239999830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1083963752353599 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48449655698 / 1000000000000) (48449655866 / 1000000000000), orderedInterval (-1451696044 / 1000000000000) (-1451695876 / 1000000000000)))) (orderedInterval (3413868281 / 1000000000000) (3413868324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (458341961972013 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56929085529 / 1000000000000) (56929177705 / 1000000000000), orderedInterval (-48362012453 / 1000000000000) (-48361920277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1863134629031373 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36936824655 / 1000000000000) (36936825372 / 1000000000000), orderedInterval (-1602197537 / 1000000000000) (-1602196820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1244487586963107 / 4000000000000) 2 (IntervalRat.scale (501 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35128626017 / 1000000000000) (-35128626016 / 1000000000000), orderedInterval (-28442422398 / 1000000000000) (-28442422397 / 1000000000000)))) (orderedInterval (129629043 / 1000000000000) (129629507 / 1000000000000))) = true
  rfl'

theorem compactCertificate379_chunkChecks2 :
    compactCertificate379.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate379.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate379_chunkChecks2_0
    compactCertificate379_chunkChecks2_1 compactCertificate379_chunkChecks2_2

theorem compactCertificate379_chunkChecks3_0 :
    compactCertificate379.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (501 / 2) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-2142535025 / 1000000000000) (-2142535021 / 1000000000000), orderedInterval (50371040188 / 1000000000000) (50371040193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (738068664898401 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3057681432 / 1000000000000) (3057681440 / 1000000000000), orderedInterval (-58667094298 / 1000000000000) (-58667094290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (238676241650433 / 800000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29009420360 / 1000000000000) (-29009420359 / 1000000000000), orderedInterval (-35899812419 / 1000000000000) (-35899812418 / 1000000000000)))) (orderedInterval (-16200286914 / 1000000000000) (-16200286885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (215366595647907 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102025413779 / 1000000000000) (-102025413778 / 1000000000000), orderedInterval (-36660536942 / 1000000000000) (-36660536941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (578504969727879 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51867987151 / 1000000000000) (51867987152 / 1000000000000), orderedInterval (41191369692 / 1000000000000) (41191369693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1570753528054443 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28155464092 / 1000000000000) (-28155464091 / 1000000000000), orderedInterval (-28747009578 / 1000000000000) (-28747009577 / 1000000000000)))) (orderedInterval (-8143528414 / 1000000000000) (-8143528342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1157009939456259 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39751259366 / 1000000000000) (39751259367 / 1000000000000), orderedInterval (24846135409 / 1000000000000) (24846135410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1982556251861007 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1883182122 / 1000000000000) (1883182123 / 1000000000000), orderedInterval (35787715555 / 1000000000000) (35787715556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1460341961972013 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41432476131 / 1000000000000) (41432476168 / 1000000000000), orderedInterval (5149375293 / 1000000000000) (5149375330 / 1000000000000)))) (orderedInterval (8172492567 / 1000000000000) (8172492650 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate379_chunkChecks3_1 :
    compactCertificate379.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2240540113454499 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33354449599 / 1000000000000) (33354453640 / 1000000000000), orderedInterval (-4931519646 / 1000000000000) (-4931515605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1293576437632971 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24871731537 / 1000000000000) (-24871731536 / 1000000000000), orderedInterval (-36703278981 / 1000000000000) (-36703278980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2295474088677639 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8490203962 / 1000000000000) (8490203971 / 1000000000000), orderedInterval (-32213989604 / 1000000000000) (-32213989595 / 1000000000000)))) (orderedInterval (51006947844 / 1000000000000) (51006956868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2144729654709891 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8350028824 / 1000000000000) (8350028834 / 1000000000000), orderedInterval (-33438264516 / 1000000000000) (-33438264506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1530580282114803 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6330772287 / 1000000000000) (6330772288 / 1000000000000), orderedInterval (40286356165 / 1000000000000) (40286356166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1735514909183637 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34545695108 / 1000000000000) (34545695109 / 1000000000000), orderedInterval (16509213125 / 1000000000000) (16509213126 / 1000000000000)))) (orderedInterval (-19063019879 / 1000000000000) (-19063019740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1446891394752453 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39465003749 / 1000000000000) (-39465003747 / 1000000000000), orderedInterval (-14174917738 / 1000000000000) (-14174917737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1278372427077513 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2869467195 / 1000000000000) (-2869467191 / 1000000000000), orderedInterval (44543665657 / 1000000000000) (44543665660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (370522156325787 / 800000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31550686189 / 1000000000000) (-31550575590 / 1000000000000), orderedInterval (19504305189 / 1000000000000) (19504415787 / 1000000000000)))) (orderedInterval (2616271939 / 1000000000000) (2616289956 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate379_chunkChecks3_2 :
    compactCertificate379.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1024883783909889 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28340042486 / 1000000000000) (-28340036068 / 1000000000000), orderedInterval (41061341366 / 1000000000000) (41061347784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (868805333897529 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50771788188 / 1000000000000) (-50771788187 / 1000000000000), orderedInterval (-18677587854 / 1000000000000) (-18677587853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (543658038027987 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68385372558 / 1000000000000) (-68385372482 / 1000000000000), orderedInterval (2968434841 / 1000000000000) (2968434917 / 1000000000000)))) (orderedInterval (6345757759 / 1000000000000) (6345758916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (292381100976429 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93199447467 / 1000000000000) (-93199447409 / 1000000000000), orderedInterval (5444997487 / 1000000000000) (5444997545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (793871565376287 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55033391635 / 1000000000000) (-55033391633 / 1000000000000), orderedInterval (-13239999832 / 1000000000000) (-13239999830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1083963752353599 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48449655698 / 1000000000000) (48449655866 / 1000000000000), orderedInterval (-1451696044 / 1000000000000) (-1451695876 / 1000000000000)))) (orderedInterval (-301363941 / 1000000000000) (-301363896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (458341961972013 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56929085529 / 1000000000000) (56929177705 / 1000000000000), orderedInterval (-48362012453 / 1000000000000) (-48361920277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1863134629031373 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36936824655 / 1000000000000) (36936825372 / 1000000000000), orderedInterval (-1602197537 / 1000000000000) (-1602196820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1244487586963107 / 4000000000000) 3 (IntervalRat.scale (501 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35128626017 / 1000000000000) (-35128626016 / 1000000000000), orderedInterval (-28442422398 / 1000000000000) (-28442422397 / 1000000000000)))) (orderedInterval (-11035161403 / 1000000000000) (-11035160751 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate379_chunkChecks3 :
    compactCertificate379.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate379.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate379_chunkChecks3_0
    compactCertificate379_chunkChecks3_1 compactCertificate379_chunkChecks3_2

theorem compactCertificate379_chunkChecks4_0 :
    compactCertificate379.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (501 / 2) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-2142535025 / 1000000000000) (-2142535021 / 1000000000000), orderedInterval (50371040188 / 1000000000000) (50371040193 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (738068664898401 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (3057681432 / 1000000000000) (3057681440 / 1000000000000), orderedInterval (-58667094298 / 1000000000000) (-58667094290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (238676241650433 / 800000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29009420360 / 1000000000000) (-29009420359 / 1000000000000), orderedInterval (-35899812419 / 1000000000000) (-35899812418 / 1000000000000)))) (orderedInterval (-4136625853 / 1000000000000) (-4136625820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (215366595647907 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-102025413779 / 1000000000000) (-102025413778 / 1000000000000), orderedInterval (-36660536942 / 1000000000000) (-36660536941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (578504969727879 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51867987151 / 1000000000000) (51867987152 / 1000000000000), orderedInterval (41191369692 / 1000000000000) (41191369693 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1570753528054443 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28155464092 / 1000000000000) (-28155464091 / 1000000000000), orderedInterval (-28747009578 / 1000000000000) (-28747009577 / 1000000000000)))) (orderedInterval (12365039754 / 1000000000000) (12365039864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1157009939456259 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39751259366 / 1000000000000) (39751259367 / 1000000000000), orderedInterval (24846135409 / 1000000000000) (24846135410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1982556251861007 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1883182122 / 1000000000000) (1883182123 / 1000000000000), orderedInterval (35787715555 / 1000000000000) (35787715556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1460341961972013 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41432476131 / 1000000000000) (41432476168 / 1000000000000), orderedInterval (5149375293 / 1000000000000) (5149375330 / 1000000000000)))) (orderedInterval (3562332441 / 1000000000000) (3562332593 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate379_chunkChecks4_1 :
    compactCertificate379.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2240540113454499 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33354449599 / 1000000000000) (33354453640 / 1000000000000), orderedInterval (-4931519646 / 1000000000000) (-4931515605 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1293576437632971 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24871731537 / 1000000000000) (-24871731536 / 1000000000000), orderedInterval (-36703278981 / 1000000000000) (-36703278980 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2295474088677639 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8490203962 / 1000000000000) (8490203971 / 1000000000000), orderedInterval (-32213989604 / 1000000000000) (-32213989595 / 1000000000000)))) (orderedInterval (-120449662937 / 1000000000000) (-120449642740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2144729654709891 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8350028824 / 1000000000000) (8350028834 / 1000000000000), orderedInterval (-33438264516 / 1000000000000) (-33438264506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1530580282114803 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6330772287 / 1000000000000) (6330772288 / 1000000000000), orderedInterval (40286356165 / 1000000000000) (40286356166 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1735514909183637 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34545695108 / 1000000000000) (34545695109 / 1000000000000), orderedInterval (16509213125 / 1000000000000) (16509213126 / 1000000000000)))) (orderedInterval (-1326007415 / 1000000000000) (-1326007175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1446891394752453 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-39465003749 / 1000000000000) (-39465003747 / 1000000000000), orderedInterval (-14174917738 / 1000000000000) (-14174917737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1278372427077513 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-2869467195 / 1000000000000) (-2869467191 / 1000000000000), orderedInterval (44543665657 / 1000000000000) (44543665660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (370522156325787 / 800000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31550686189 / 1000000000000) (-31550575590 / 1000000000000), orderedInterval (19504305189 / 1000000000000) (19504415787 / 1000000000000)))) (orderedInterval (-11007406614 / 1000000000000) (-11007373252 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate379_chunkChecks4_2 :
    compactCertificate379.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1024883783909889 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-28340042486 / 1000000000000) (-28340036068 / 1000000000000), orderedInterval (41061341366 / 1000000000000) (41061347784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (868805333897529 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50771788188 / 1000000000000) (-50771788187 / 1000000000000), orderedInterval (-18677587854 / 1000000000000) (-18677587853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (543658038027987 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68385372558 / 1000000000000) (-68385372482 / 1000000000000), orderedInterval (2968434841 / 1000000000000) (2968434917 / 1000000000000)))) (orderedInterval (6340272429 / 1000000000000) (6340273615 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (292381100976429 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93199447467 / 1000000000000) (-93199447409 / 1000000000000), orderedInterval (5444997487 / 1000000000000) (5444997545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (793871565376287 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55033391635 / 1000000000000) (-55033391633 / 1000000000000), orderedInterval (-13239999832 / 1000000000000) (-13239999830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1083963752353599 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48449655698 / 1000000000000) (48449655866 / 1000000000000), orderedInterval (-1451696044 / 1000000000000) (-1451695876 / 1000000000000)))) (orderedInterval (-4578534971 / 1000000000000) (-4578534923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (458341961972013 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56929085529 / 1000000000000) (56929177705 / 1000000000000), orderedInterval (-48362012453 / 1000000000000) (-48361920277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1863134629031373 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36936824655 / 1000000000000) (36936825372 / 1000000000000), orderedInterval (-1602197537 / 1000000000000) (-1602196820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1244487586963107 / 4000000000000) 4 (IntervalRat.scale (501 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35128626017 / 1000000000000) (-35128626016 / 1000000000000), orderedInterval (-28442422398 / 1000000000000) (-28442422397 / 1000000000000)))) (orderedInterval (-20155005575 / 1000000000000) (-20155004492 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate379_chunkChecks4 :
    compactCertificate379.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate379.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate379_chunkChecks4_0
    compactCertificate379_chunkChecks4_1 compactCertificate379_chunkChecks4_2

theorem compactCertificate379_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate379.chunkCheck r b = true :=
  compactCertificate379.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate379_chunkChecks0
    · exact compactCertificate379_chunkChecks1
    · exact compactCertificate379_chunkChecks2
    · exact compactCertificate379_chunkChecks3
    · exact compactCertificate379_chunkChecks4)

theorem compactCertificate379_coefficient0 :
    compactCertificate379.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate379_coefficient1 :
    compactCertificate379.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate379_coefficient2 :
    compactCertificate379.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate379_coefficient3 :
    compactCertificate379.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate379_coefficient4 :
    compactCertificate379.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate379_coefficients : ∀ r : Fin 5,
    compactCertificate379.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate379_coefficient0
  · exact compactCertificate379_coefficient1
  · exact compactCertificate379_coefficient2
  · exact compactCertificate379_coefficient3
  · exact compactCertificate379_coefficient4

theorem compactCertificate379_lower : (1 : ℚ) ≤ compactCertificate379.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate379, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate379_proves {t : ℝ} (ht : t ∈ compactCertificate379.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate379.proves compactCertificate379_states compactCertificate379_chunks
    compactCertificate379_coefficients compactCertificate379_lower ht

end Erdos232
