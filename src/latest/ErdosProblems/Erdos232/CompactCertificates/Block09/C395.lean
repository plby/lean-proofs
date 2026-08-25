/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate395 : CompactCertificate where
  left := 266
  right := 267
  center := 533 / 2
  grid := fun i =>
    match i.val with
    | 0 => 85
    | 1 => 63
    | 2 => 101
    | 3 => 18
    | 4 => 49
    | 5 => 133
    | 6 => 98
    | 7 => 168
    | 8 => 124
    | 9 => 190
    | 10 => 110
    | 11 => 194
    | 12 => 182
    | 13 => 130
    | 14 => 147
    | 15 => 123
    | 16 => 108
    | 17 => 157
    | 18 => 87
    | 19 => 74
    | 20 => 46
    | 21 => 25
    | 22 => 67
    | 23 => 92
    | 24 => 39
    | 25 => 158
    | _ => 105
  point := fun i =>
    match i.val with
    | 0 => 533 / 2
    | 1 => 785210775231233 / 4000000000000
    | 2 => 253921031536289 / 800000000000
    | 3 => 229122545868931 / 4000000000000
    | 4 => 615455386956007 / 4000000000000
    | 5 => 1671081098708619 / 4000000000000
    | 6 => 1230910773912547 / 4000000000000
    | 7 => 2109186591301231 / 4000000000000
    | 8 => 1553617296868429 / 4000000000000
    | 9 => 2383648464014467 / 4000000000000
    | 10 => 1376200082352043 / 4000000000000
    | 11 => 2442091196138087 / 4000000000000
    | 12 => 2281718375170403 / 4000000000000
    | 13 => 1628341896940499 / 4000000000000
    | 14 => 1846366160868021 / 4000000000000
    | 15 => 1539307611582949 / 4000000000000
    | 16 => 1360024957349929 / 4000000000000
    | 17 => 394188242158971 / 800000000000
    | 18 => 1090345422802337 / 4000000000000
    | 19 => 924297890154457 / 4000000000000
    | 20 => 578382703131571 / 4000000000000
    | 21 => 311056141358157 / 4000000000000
    | 22 => 844577932825471 / 4000000000000
    | 23 => 1153198962084767 / 4000000000000
    | 24 => 487617296868429 / 4000000000000
    | 25 => 1982137240067309 / 4000000000000
    | _ => 1323975816070531 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-12070845854 / 1000000000000) (-12070845853 / 1000000000000), orderedInterval (-47338893699 / 1000000000000) (-47338893698 / 1000000000000))
    | 1 => (orderedInterval (42134047080 / 1000000000000) (42134119641 / 1000000000000), orderedInterval (-38418833803 / 1000000000000) (-38418761241 / 1000000000000))
    | 2 => (orderedInterval (-34672367234 / 1000000000000) (-34672367233 / 1000000000000), orderedInterval (-28292368143 / 1000000000000) (-28292368142 / 1000000000000))
    | 3 => (orderedInterval (105258208605 / 1000000000000) (105258208616 / 1000000000000), orderedInterval (4941092224 / 1000000000000) (4941092234 / 1000000000000))
    | 4 => (orderedInterval (-41947464291 / 1000000000000) (-41947464290 / 1000000000000), orderedInterval (-48628082558 / 1000000000000) (-48628082557 / 1000000000000))
    | 5 => (orderedInterval (-25844128757 / 1000000000000) (-25844128756 / 1000000000000), orderedInterval (-29225391997 / 1000000000000) (-29225391996 / 1000000000000))
    | 6 => (orderedInterval (27038702296 / 1000000000000) (27038702297 / 1000000000000), orderedInterval (36530453421 / 1000000000000) (36530453422 / 1000000000000))
    | 7 => (orderedInterval (10077059040 / 1000000000000) (10077059041 / 1000000000000), orderedInterval (33243728465 / 1000000000000) (33243728466 / 1000000000000))
    | 8 => (orderedInterval (-14567948237 / 1000000000000) (-14567948058 / 1000000000000), orderedInterval (37792295498 / 1000000000000) (37792295677 / 1000000000000))
    | 9 => (orderedInterval (-6663191330 / 1000000000000) (-6663191326 / 1000000000000), orderedInterval (32004242840 / 1000000000000) (32004242843 / 1000000000000))
    | 10 => (orderedInterval (-29009445187 / 1000000000000) (-29009429300 / 1000000000000), orderedInterval (31804117168 / 1000000000000) (31804133055 / 1000000000000))
    | 11 => (orderedInterval (31136928611 / 1000000000000) (31136946574 / 1000000000000), orderedInterval (-8583317776 / 1000000000000) (-8583299812 / 1000000000000))
    | 12 => (orderedInterval (-17606213949 / 1000000000000) (-17606213340 / 1000000000000), orderedInterval (28406576818 / 1000000000000) (28406577428 / 1000000000000))
    | 13 => (orderedInterval (-20212235054 / 1000000000000) (-20212233738 / 1000000000000), orderedInterval (34014736037 / 1000000000000) (34014737353 / 1000000000000))
    | 14 => (orderedInterval (-19806944989 / 1000000000000) (-19806944988 / 1000000000000), orderedInterval (-31393024238 / 1000000000000) (-31393024237 / 1000000000000))
    | 15 => (orderedInterval (29287938049 / 1000000000000) (29287961956 / 1000000000000), orderedInterval (-28260707343 / 1000000000000) (-28260683435 / 1000000000000))
    | 16 => (orderedInterval (43160284277 / 1000000000000) (43160284345 / 1000000000000), orderedInterval (3029197311 / 1000000000000) (3029197379 / 1000000000000))
    | 17 => (orderedInterval (-10292221488 / 1000000000000) (-10292221487 / 1000000000000), orderedInterval (-34429103450 / 1000000000000) (-34429103449 / 1000000000000))
    | 18 => (orderedInterval (-2547303107 / 1000000000000) (-2547303105 / 1000000000000), orderedInterval (-48254983418 / 1000000000000) (-48254983417 / 1000000000000))
    | 19 => (orderedInterval (-30434651202 / 1000000000000) (-30434642791 / 1000000000000), orderedInterval (42830039580 / 1000000000000) (42830047991 / 1000000000000))
    | 20 => (orderedInterval (50584737542 / 1000000000000) (50584737543 / 1000000000000), orderedInterval (42766184362 / 1000000000000) (42766184363 / 1000000000000))
    | 21 => (orderedInterval (-724715016 / 1000000000000) (-724715009 / 1000000000000), orderedInterval (-90472971832 / 1000000000000) (-90472971825 / 1000000000000))
    | 22 => (orderedInterval (-54459051304 / 1000000000000) (-54459051293 / 1000000000000), orderedInterval (-6892027460 / 1000000000000) (-6892027449 / 1000000000000))
    | 23 => (orderedInterval (2732458666 / 1000000000000) (2732458668 / 1000000000000), orderedInterval (46907136811 / 1000000000000) (46907136813 / 1000000000000))
    | 24 => (orderedInterval (-11982578073 / 1000000000000) (-11982578072 / 1000000000000), orderedInterval (-71216200129 / 1000000000000) (-71216200128 / 1000000000000))
    | 25 => (orderedInterval (-1869553215 / 1000000000000) (-1869553214 / 1000000000000), orderedInterval (35796009284 / 1000000000000) (35796009286 / 1000000000000))
    | _ => (orderedInterval (-41331619234 / 1000000000000) (-41331610077 / 1000000000000), orderedInterval (14727137385 / 1000000000000) (14727146541 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-6426467199 / 1000000000000) (-6426466503 / 1000000000000)
      | 1 => orderedInterval (-836302278 / 1000000000000) (-836302245 / 1000000000000)
      | 2 => orderedInterval (-662895393 / 1000000000000) (-662895373 / 1000000000000)
      | 3 => orderedInterval (3460905285 / 1000000000000) (3460909123 / 1000000000000)
      | 4 => orderedInterval (-1493245857 / 1000000000000) (-1493245689 / 1000000000000)
      | 5 => orderedInterval (-2395233745 / 1000000000000) (-2395233439 / 1000000000000)
      | 6 => orderedInterval (3776693762 / 1000000000000) (3776694306 / 1000000000000)
      | 7 => orderedInterval (1039474368 / 1000000000000) (1039474401 / 1000000000000)
      | _ => orderedInterval (7834856460 / 1000000000000) (7834858252 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-21004504088 / 1000000000000) (-21004503568 / 1000000000000)
      | 1 => orderedInterval (2220313815 / 1000000000000) (2220313853 / 1000000000000)
      | 2 => orderedInterval (-697632094 / 1000000000000) (-697632061 / 1000000000000)
      | 3 => orderedInterval (-12469145621 / 1000000000000) (-12469138031 / 1000000000000)
      | 4 => orderedInterval (4090818866 / 1000000000000) (4090819132 / 1000000000000)
      | 5 => orderedInterval (-2322264129 / 1000000000000) (-2322263688 / 1000000000000)
      | 6 => orderedInterval (6545286441 / 1000000000000) (6545286917 / 1000000000000)
      | 7 => orderedInterval (-3277618204 / 1000000000000) (-3277618175 / 1000000000000)
      | _ => orderedInterval (-9046363676 / 1000000000000) (-9046361438 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (7536315794 / 1000000000000) (7536316188 / 1000000000000)
      | 1 => orderedInterval (-3959957089 / 1000000000000) (-3959957038 / 1000000000000)
      | 2 => orderedInterval (1967268149 / 1000000000000) (1967268205 / 1000000000000)
      | 3 => orderedInterval (-25520843032 / 1000000000000) (-25520827168 / 1000000000000)
      | 4 => orderedInterval (2687488206 / 1000000000000) (2687488633 / 1000000000000)
      | 5 => orderedInterval (4224678675 / 1000000000000) (4224679314 / 1000000000000)
      | 6 => orderedInterval (-2230536632 / 1000000000000) (-2230536213 / 1000000000000)
      | 7 => orderedInterval (-519316493 / 1000000000000) (-519316463 / 1000000000000)
      | _ => orderedInterval (-12439620118 / 1000000000000) (-12439617306 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (21682780446 / 1000000000000) (21682780746 / 1000000000000)
      | 1 => orderedInterval (-7646524551 / 1000000000000) (-7646524475 / 1000000000000)
      | 2 => orderedInterval (5107530593 / 1000000000000) (5107530691 / 1000000000000)
      | 3 => orderedInterval (73275465558 / 1000000000000) (73275499886 / 1000000000000)
      | 4 => orderedInterval (-7270927694 / 1000000000000) (-7270926997 / 1000000000000)
      | 5 => orderedInterval (6898347368 / 1000000000000) (6898348295 / 1000000000000)
      | 6 => orderedInterval (-6890058796 / 1000000000000) (-6890058426 / 1000000000000)
      | 7 => orderedInterval (4433867402 / 1000000000000) (4433867432 / 1000000000000)
      | _ => orderedInterval (24114205857 / 1000000000000) (24114209396 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8925310496 / 1000000000000) (-8925310261 / 1000000000000)
      | 1 => orderedInterval (10979772800 / 1000000000000) (10979772917 / 1000000000000)
      | 2 => orderedInterval (-6390406360 / 1000000000000) (-6390406183 / 1000000000000)
      | 3 => orderedInterval (144994112349 / 1000000000000) (144994188503 / 1000000000000)
      | 4 => orderedInterval (-2777694755 / 1000000000000) (-2777693591 / 1000000000000)
      | 5 => orderedInterval (-8204726663 / 1000000000000) (-8204725312 / 1000000000000)
      | 6 => orderedInterval (1613839175 / 1000000000000) (1613839504 / 1000000000000)
      | 7 => orderedInterval (166834272 / 1000000000000) (166834303 / 1000000000000)
      | _ => orderedInterval (20087923069 / 1000000000000) (20087927562 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4297785403 / 1000000000000) (4297792833 / 1000000000000)
    | 1 => orderedInterval (-35961108690 / 1000000000000) (-35961097059 / 1000000000000)
    | 2 => orderedInterval (-28254522540 / 1000000000000) (-28254501848 / 1000000000000)
    | 3 => orderedInterval (113704686183 / 1000000000000) (113704726548 / 1000000000000)
    | _ => orderedInterval (151544343391 / 1000000000000) (151544427442 / 1000000000000)

theorem compactCertificate395_stateChecks0 :
    compactCertificate395.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (533 / 2)) (orderedInterval (-12070845854 / 1000000000000) (-12070845853 / 1000000000000), orderedInterval (-47338893699 / 1000000000000) (-47338893698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (785210775231233 / 4000000000000)) (orderedInterval (42134047080 / 1000000000000) (42134119641 / 1000000000000), orderedInterval (-38418833803 / 1000000000000) (-38418761241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (253921031536289 / 800000000000)) (orderedInterval (-34672367234 / 1000000000000) (-34672367233 / 1000000000000), orderedInterval (-28292368143 / 1000000000000) (-28292368142 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks1 :
    compactCertificate395.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (229122545868931 / 4000000000000)) (orderedInterval (105258208605 / 1000000000000) (105258208616 / 1000000000000), orderedInterval (4941092224 / 1000000000000) (4941092234 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (615455386956007 / 4000000000000)) (orderedInterval (-41947464291 / 1000000000000) (-41947464290 / 1000000000000), orderedInterval (-48628082558 / 1000000000000) (-48628082557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1671081098708619 / 4000000000000)) (orderedInterval (-25844128757 / 1000000000000) (-25844128756 / 1000000000000), orderedInterval (-29225391997 / 1000000000000) (-29225391996 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks2 :
    compactCertificate395.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1230910773912547 / 4000000000000)) (orderedInterval (27038702296 / 1000000000000) (27038702297 / 1000000000000), orderedInterval (36530453421 / 1000000000000) (36530453422 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2109186591301231 / 4000000000000)) (orderedInterval (10077059040 / 1000000000000) (10077059041 / 1000000000000), orderedInterval (33243728465 / 1000000000000) (33243728466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1553617296868429 / 4000000000000)) (orderedInterval (-14567948237 / 1000000000000) (-14567948058 / 1000000000000), orderedInterval (37792295498 / 1000000000000) (37792295677 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks3 :
    compactCertificate395.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2383648464014467 / 4000000000000)) (orderedInterval (-6663191330 / 1000000000000) (-6663191326 / 1000000000000), orderedInterval (32004242840 / 1000000000000) (32004242843 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1376200082352043 / 4000000000000)) (orderedInterval (-29009445187 / 1000000000000) (-29009429300 / 1000000000000), orderedInterval (31804117168 / 1000000000000) (31804133055 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2442091196138087 / 4000000000000)) (orderedInterval (31136928611 / 1000000000000) (31136946574 / 1000000000000), orderedInterval (-8583317776 / 1000000000000) (-8583299812 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks4 :
    compactCertificate395.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2281718375170403 / 4000000000000)) (orderedInterval (-17606213949 / 1000000000000) (-17606213340 / 1000000000000), orderedInterval (28406576818 / 1000000000000) (28406577428 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1628341896940499 / 4000000000000)) (orderedInterval (-20212235054 / 1000000000000) (-20212233738 / 1000000000000), orderedInterval (34014736037 / 1000000000000) (34014737353 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1846366160868021 / 4000000000000)) (orderedInterval (-19806944989 / 1000000000000) (-19806944988 / 1000000000000), orderedInterval (-31393024238 / 1000000000000) (-31393024237 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks5 :
    compactCertificate395.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1539307611582949 / 4000000000000)) (orderedInterval (29287938049 / 1000000000000) (29287961956 / 1000000000000), orderedInterval (-28260707343 / 1000000000000) (-28260683435 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1360024957349929 / 4000000000000)) (orderedInterval (43160284277 / 1000000000000) (43160284345 / 1000000000000), orderedInterval (3029197311 / 1000000000000) (3029197379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (394188242158971 / 800000000000)) (orderedInterval (-10292221488 / 1000000000000) (-10292221487 / 1000000000000), orderedInterval (-34429103450 / 1000000000000) (-34429103449 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks6 :
    compactCertificate395.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1090345422802337 / 4000000000000)) (orderedInterval (-2547303107 / 1000000000000) (-2547303105 / 1000000000000), orderedInterval (-48254983418 / 1000000000000) (-48254983417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (924297890154457 / 4000000000000)) (orderedInterval (-30434651202 / 1000000000000) (-30434642791 / 1000000000000), orderedInterval (42830039580 / 1000000000000) (42830047991 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (578382703131571 / 4000000000000)) (orderedInterval (50584737542 / 1000000000000) (50584737543 / 1000000000000), orderedInterval (42766184362 / 1000000000000) (42766184363 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks7 :
    compactCertificate395.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (311056141358157 / 4000000000000)) (orderedInterval (-724715016 / 1000000000000) (-724715009 / 1000000000000), orderedInterval (-90472971832 / 1000000000000) (-90472971825 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844577932825471 / 4000000000000)) (orderedInterval (-54459051304 / 1000000000000) (-54459051293 / 1000000000000), orderedInterval (-6892027460 / 1000000000000) (-6892027449 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1153198962084767 / 4000000000000)) (orderedInterval (2732458666 / 1000000000000) (2732458668 / 1000000000000), orderedInterval (46907136811 / 1000000000000) (46907136813 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_stateChecks8 :
    compactCertificate395.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (487617296868429 / 4000000000000)) (orderedInterval (-11982578073 / 1000000000000) (-11982578072 / 1000000000000), orderedInterval (-71216200129 / 1000000000000) (-71216200128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1982137240067309 / 4000000000000)) (orderedInterval (-1869553215 / 1000000000000) (-1869553214 / 1000000000000), orderedInterval (35796009284 / 1000000000000) (35796009286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1323975816070531 / 4000000000000)) (orderedInterval (-41331619234 / 1000000000000) (-41331610077 / 1000000000000), orderedInterval (14727137385 / 1000000000000) (14727146541 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_states : ∀ j,
    BesselStateValid (compactCertificate395.point j) (compactCertificate395.state j) :=
  compactCertificate395.statesValid_of_checks3 compactCertificate395_stateChecks0
    compactCertificate395_stateChecks1 compactCertificate395_stateChecks2
    compactCertificate395_stateChecks3 compactCertificate395_stateChecks4
    compactCertificate395_stateChecks5 compactCertificate395_stateChecks6
    compactCertificate395_stateChecks7 compactCertificate395_stateChecks8

theorem compactCertificate395_chunkChecks0_0 :
    compactCertificate395.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (533 / 2) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12070845854 / 1000000000000) (-12070845853 / 1000000000000), orderedInterval (-47338893699 / 1000000000000) (-47338893698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (785210775231233 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42134047080 / 1000000000000) (42134119641 / 1000000000000), orderedInterval (-38418833803 / 1000000000000) (-38418761241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (253921031536289 / 800000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34672367234 / 1000000000000) (-34672367233 / 1000000000000), orderedInterval (-28292368143 / 1000000000000) (-28292368142 / 1000000000000)))) (orderedInterval (-6426467199 / 1000000000000) (-6426466503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (229122545868931 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105258208605 / 1000000000000) (105258208616 / 1000000000000), orderedInterval (4941092224 / 1000000000000) (4941092234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (615455386956007 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41947464291 / 1000000000000) (-41947464290 / 1000000000000), orderedInterval (-48628082558 / 1000000000000) (-48628082557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1671081098708619 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25844128757 / 1000000000000) (-25844128756 / 1000000000000), orderedInterval (-29225391997 / 1000000000000) (-29225391996 / 1000000000000)))) (orderedInterval (-836302278 / 1000000000000) (-836302245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1230910773912547 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27038702296 / 1000000000000) (27038702297 / 1000000000000), orderedInterval (36530453421 / 1000000000000) (36530453422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2109186591301231 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10077059040 / 1000000000000) (10077059041 / 1000000000000), orderedInterval (33243728465 / 1000000000000) (33243728466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1553617296868429 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14567948237 / 1000000000000) (-14567948058 / 1000000000000), orderedInterval (37792295498 / 1000000000000) (37792295677 / 1000000000000)))) (orderedInterval (-662895393 / 1000000000000) (-662895373 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks0_1 :
    compactCertificate395.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2383648464014467 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6663191330 / 1000000000000) (-6663191326 / 1000000000000), orderedInterval (32004242840 / 1000000000000) (32004242843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1376200082352043 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29009445187 / 1000000000000) (-29009429300 / 1000000000000), orderedInterval (31804117168 / 1000000000000) (31804133055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2442091196138087 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31136928611 / 1000000000000) (31136946574 / 1000000000000), orderedInterval (-8583317776 / 1000000000000) (-8583299812 / 1000000000000)))) (orderedInterval (3460905285 / 1000000000000) (3460909123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2281718375170403 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17606213949 / 1000000000000) (-17606213340 / 1000000000000), orderedInterval (28406576818 / 1000000000000) (28406577428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1628341896940499 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20212235054 / 1000000000000) (-20212233738 / 1000000000000), orderedInterval (34014736037 / 1000000000000) (34014737353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1846366160868021 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19806944989 / 1000000000000) (-19806944988 / 1000000000000), orderedInterval (-31393024238 / 1000000000000) (-31393024237 / 1000000000000)))) (orderedInterval (-1493245857 / 1000000000000) (-1493245689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1539307611582949 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29287938049 / 1000000000000) (29287961956 / 1000000000000), orderedInterval (-28260707343 / 1000000000000) (-28260683435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1360024957349929 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43160284277 / 1000000000000) (43160284345 / 1000000000000), orderedInterval (3029197311 / 1000000000000) (3029197379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (394188242158971 / 800000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10292221488 / 1000000000000) (-10292221487 / 1000000000000), orderedInterval (-34429103450 / 1000000000000) (-34429103449 / 1000000000000)))) (orderedInterval (-2395233745 / 1000000000000) (-2395233439 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks0_2 :
    compactCertificate395.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1090345422802337 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2547303107 / 1000000000000) (-2547303105 / 1000000000000), orderedInterval (-48254983418 / 1000000000000) (-48254983417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (924297890154457 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30434651202 / 1000000000000) (-30434642791 / 1000000000000), orderedInterval (42830039580 / 1000000000000) (42830047991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (578382703131571 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50584737542 / 1000000000000) (50584737543 / 1000000000000), orderedInterval (42766184362 / 1000000000000) (42766184363 / 1000000000000)))) (orderedInterval (3776693762 / 1000000000000) (3776694306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (311056141358157 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-724715016 / 1000000000000) (-724715009 / 1000000000000), orderedInterval (-90472971832 / 1000000000000) (-90472971825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (844577932825471 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54459051304 / 1000000000000) (-54459051293 / 1000000000000), orderedInterval (-6892027460 / 1000000000000) (-6892027449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1153198962084767 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2732458666 / 1000000000000) (2732458668 / 1000000000000), orderedInterval (46907136811 / 1000000000000) (46907136813 / 1000000000000)))) (orderedInterval (1039474368 / 1000000000000) (1039474401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (487617296868429 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11982578073 / 1000000000000) (-11982578072 / 1000000000000), orderedInterval (-71216200129 / 1000000000000) (-71216200128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1982137240067309 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1869553215 / 1000000000000) (-1869553214 / 1000000000000), orderedInterval (35796009284 / 1000000000000) (35796009286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1323975816070531 / 4000000000000) 0 (IntervalRat.scale (533 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41331619234 / 1000000000000) (-41331610077 / 1000000000000), orderedInterval (14727137385 / 1000000000000) (14727146541 / 1000000000000)))) (orderedInterval (7834856460 / 1000000000000) (7834858252 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks0 :
    compactCertificate395.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate395.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate395_chunkChecks0_0
    compactCertificate395_chunkChecks0_1 compactCertificate395_chunkChecks0_2

theorem compactCertificate395_chunkChecks1_0 :
    compactCertificate395.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (533 / 2) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12070845854 / 1000000000000) (-12070845853 / 1000000000000), orderedInterval (-47338893699 / 1000000000000) (-47338893698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (785210775231233 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42134047080 / 1000000000000) (42134119641 / 1000000000000), orderedInterval (-38418833803 / 1000000000000) (-38418761241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (253921031536289 / 800000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34672367234 / 1000000000000) (-34672367233 / 1000000000000), orderedInterval (-28292368143 / 1000000000000) (-28292368142 / 1000000000000)))) (orderedInterval (-21004504088 / 1000000000000) (-21004503568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (229122545868931 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105258208605 / 1000000000000) (105258208616 / 1000000000000), orderedInterval (4941092224 / 1000000000000) (4941092234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (615455386956007 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41947464291 / 1000000000000) (-41947464290 / 1000000000000), orderedInterval (-48628082558 / 1000000000000) (-48628082557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1671081098708619 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25844128757 / 1000000000000) (-25844128756 / 1000000000000), orderedInterval (-29225391997 / 1000000000000) (-29225391996 / 1000000000000)))) (orderedInterval (2220313815 / 1000000000000) (2220313853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1230910773912547 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27038702296 / 1000000000000) (27038702297 / 1000000000000), orderedInterval (36530453421 / 1000000000000) (36530453422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2109186591301231 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10077059040 / 1000000000000) (10077059041 / 1000000000000), orderedInterval (33243728465 / 1000000000000) (33243728466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1553617296868429 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14567948237 / 1000000000000) (-14567948058 / 1000000000000), orderedInterval (37792295498 / 1000000000000) (37792295677 / 1000000000000)))) (orderedInterval (-697632094 / 1000000000000) (-697632061 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks1_1 :
    compactCertificate395.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2383648464014467 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6663191330 / 1000000000000) (-6663191326 / 1000000000000), orderedInterval (32004242840 / 1000000000000) (32004242843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1376200082352043 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29009445187 / 1000000000000) (-29009429300 / 1000000000000), orderedInterval (31804117168 / 1000000000000) (31804133055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2442091196138087 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31136928611 / 1000000000000) (31136946574 / 1000000000000), orderedInterval (-8583317776 / 1000000000000) (-8583299812 / 1000000000000)))) (orderedInterval (-12469145621 / 1000000000000) (-12469138031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2281718375170403 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17606213949 / 1000000000000) (-17606213340 / 1000000000000), orderedInterval (28406576818 / 1000000000000) (28406577428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1628341896940499 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20212235054 / 1000000000000) (-20212233738 / 1000000000000), orderedInterval (34014736037 / 1000000000000) (34014737353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1846366160868021 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19806944989 / 1000000000000) (-19806944988 / 1000000000000), orderedInterval (-31393024238 / 1000000000000) (-31393024237 / 1000000000000)))) (orderedInterval (4090818866 / 1000000000000) (4090819132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1539307611582949 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29287938049 / 1000000000000) (29287961956 / 1000000000000), orderedInterval (-28260707343 / 1000000000000) (-28260683435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1360024957349929 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43160284277 / 1000000000000) (43160284345 / 1000000000000), orderedInterval (3029197311 / 1000000000000) (3029197379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (394188242158971 / 800000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10292221488 / 1000000000000) (-10292221487 / 1000000000000), orderedInterval (-34429103450 / 1000000000000) (-34429103449 / 1000000000000)))) (orderedInterval (-2322264129 / 1000000000000) (-2322263688 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks1_2 :
    compactCertificate395.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1090345422802337 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2547303107 / 1000000000000) (-2547303105 / 1000000000000), orderedInterval (-48254983418 / 1000000000000) (-48254983417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (924297890154457 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30434651202 / 1000000000000) (-30434642791 / 1000000000000), orderedInterval (42830039580 / 1000000000000) (42830047991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (578382703131571 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50584737542 / 1000000000000) (50584737543 / 1000000000000), orderedInterval (42766184362 / 1000000000000) (42766184363 / 1000000000000)))) (orderedInterval (6545286441 / 1000000000000) (6545286917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (311056141358157 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-724715016 / 1000000000000) (-724715009 / 1000000000000), orderedInterval (-90472971832 / 1000000000000) (-90472971825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (844577932825471 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54459051304 / 1000000000000) (-54459051293 / 1000000000000), orderedInterval (-6892027460 / 1000000000000) (-6892027449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1153198962084767 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2732458666 / 1000000000000) (2732458668 / 1000000000000), orderedInterval (46907136811 / 1000000000000) (46907136813 / 1000000000000)))) (orderedInterval (-3277618204 / 1000000000000) (-3277618175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (487617296868429 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11982578073 / 1000000000000) (-11982578072 / 1000000000000), orderedInterval (-71216200129 / 1000000000000) (-71216200128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1982137240067309 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1869553215 / 1000000000000) (-1869553214 / 1000000000000), orderedInterval (35796009284 / 1000000000000) (35796009286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1323975816070531 / 4000000000000) 1 (IntervalRat.scale (533 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41331619234 / 1000000000000) (-41331610077 / 1000000000000), orderedInterval (14727137385 / 1000000000000) (14727146541 / 1000000000000)))) (orderedInterval (-9046363676 / 1000000000000) (-9046361438 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks1 :
    compactCertificate395.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate395.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate395_chunkChecks1_0
    compactCertificate395_chunkChecks1_1 compactCertificate395_chunkChecks1_2

theorem compactCertificate395_chunkChecks2_0 :
    compactCertificate395.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (533 / 2) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12070845854 / 1000000000000) (-12070845853 / 1000000000000), orderedInterval (-47338893699 / 1000000000000) (-47338893698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (785210775231233 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42134047080 / 1000000000000) (42134119641 / 1000000000000), orderedInterval (-38418833803 / 1000000000000) (-38418761241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (253921031536289 / 800000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34672367234 / 1000000000000) (-34672367233 / 1000000000000), orderedInterval (-28292368143 / 1000000000000) (-28292368142 / 1000000000000)))) (orderedInterval (7536315794 / 1000000000000) (7536316188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (229122545868931 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105258208605 / 1000000000000) (105258208616 / 1000000000000), orderedInterval (4941092224 / 1000000000000) (4941092234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (615455386956007 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41947464291 / 1000000000000) (-41947464290 / 1000000000000), orderedInterval (-48628082558 / 1000000000000) (-48628082557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1671081098708619 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25844128757 / 1000000000000) (-25844128756 / 1000000000000), orderedInterval (-29225391997 / 1000000000000) (-29225391996 / 1000000000000)))) (orderedInterval (-3959957089 / 1000000000000) (-3959957038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1230910773912547 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27038702296 / 1000000000000) (27038702297 / 1000000000000), orderedInterval (36530453421 / 1000000000000) (36530453422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2109186591301231 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10077059040 / 1000000000000) (10077059041 / 1000000000000), orderedInterval (33243728465 / 1000000000000) (33243728466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1553617296868429 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14567948237 / 1000000000000) (-14567948058 / 1000000000000), orderedInterval (37792295498 / 1000000000000) (37792295677 / 1000000000000)))) (orderedInterval (1967268149 / 1000000000000) (1967268205 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks2_1 :
    compactCertificate395.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2383648464014467 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6663191330 / 1000000000000) (-6663191326 / 1000000000000), orderedInterval (32004242840 / 1000000000000) (32004242843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1376200082352043 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29009445187 / 1000000000000) (-29009429300 / 1000000000000), orderedInterval (31804117168 / 1000000000000) (31804133055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2442091196138087 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31136928611 / 1000000000000) (31136946574 / 1000000000000), orderedInterval (-8583317776 / 1000000000000) (-8583299812 / 1000000000000)))) (orderedInterval (-25520843032 / 1000000000000) (-25520827168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2281718375170403 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17606213949 / 1000000000000) (-17606213340 / 1000000000000), orderedInterval (28406576818 / 1000000000000) (28406577428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1628341896940499 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20212235054 / 1000000000000) (-20212233738 / 1000000000000), orderedInterval (34014736037 / 1000000000000) (34014737353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1846366160868021 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19806944989 / 1000000000000) (-19806944988 / 1000000000000), orderedInterval (-31393024238 / 1000000000000) (-31393024237 / 1000000000000)))) (orderedInterval (2687488206 / 1000000000000) (2687488633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1539307611582949 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29287938049 / 1000000000000) (29287961956 / 1000000000000), orderedInterval (-28260707343 / 1000000000000) (-28260683435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1360024957349929 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43160284277 / 1000000000000) (43160284345 / 1000000000000), orderedInterval (3029197311 / 1000000000000) (3029197379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (394188242158971 / 800000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10292221488 / 1000000000000) (-10292221487 / 1000000000000), orderedInterval (-34429103450 / 1000000000000) (-34429103449 / 1000000000000)))) (orderedInterval (4224678675 / 1000000000000) (4224679314 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks2_2 :
    compactCertificate395.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1090345422802337 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2547303107 / 1000000000000) (-2547303105 / 1000000000000), orderedInterval (-48254983418 / 1000000000000) (-48254983417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (924297890154457 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30434651202 / 1000000000000) (-30434642791 / 1000000000000), orderedInterval (42830039580 / 1000000000000) (42830047991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (578382703131571 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50584737542 / 1000000000000) (50584737543 / 1000000000000), orderedInterval (42766184362 / 1000000000000) (42766184363 / 1000000000000)))) (orderedInterval (-2230536632 / 1000000000000) (-2230536213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (311056141358157 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-724715016 / 1000000000000) (-724715009 / 1000000000000), orderedInterval (-90472971832 / 1000000000000) (-90472971825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (844577932825471 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54459051304 / 1000000000000) (-54459051293 / 1000000000000), orderedInterval (-6892027460 / 1000000000000) (-6892027449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1153198962084767 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2732458666 / 1000000000000) (2732458668 / 1000000000000), orderedInterval (46907136811 / 1000000000000) (46907136813 / 1000000000000)))) (orderedInterval (-519316493 / 1000000000000) (-519316463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (487617296868429 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11982578073 / 1000000000000) (-11982578072 / 1000000000000), orderedInterval (-71216200129 / 1000000000000) (-71216200128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1982137240067309 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1869553215 / 1000000000000) (-1869553214 / 1000000000000), orderedInterval (35796009284 / 1000000000000) (35796009286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1323975816070531 / 4000000000000) 2 (IntervalRat.scale (533 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41331619234 / 1000000000000) (-41331610077 / 1000000000000), orderedInterval (14727137385 / 1000000000000) (14727146541 / 1000000000000)))) (orderedInterval (-12439620118 / 1000000000000) (-12439617306 / 1000000000000))) = true
  rfl'

theorem compactCertificate395_chunkChecks2 :
    compactCertificate395.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate395.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate395_chunkChecks2_0
    compactCertificate395_chunkChecks2_1 compactCertificate395_chunkChecks2_2

theorem compactCertificate395_chunkChecks3_0 :
    compactCertificate395.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (533 / 2) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12070845854 / 1000000000000) (-12070845853 / 1000000000000), orderedInterval (-47338893699 / 1000000000000) (-47338893698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (785210775231233 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42134047080 / 1000000000000) (42134119641 / 1000000000000), orderedInterval (-38418833803 / 1000000000000) (-38418761241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (253921031536289 / 800000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34672367234 / 1000000000000) (-34672367233 / 1000000000000), orderedInterval (-28292368143 / 1000000000000) (-28292368142 / 1000000000000)))) (orderedInterval (21682780446 / 1000000000000) (21682780746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (229122545868931 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105258208605 / 1000000000000) (105258208616 / 1000000000000), orderedInterval (4941092224 / 1000000000000) (4941092234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (615455386956007 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41947464291 / 1000000000000) (-41947464290 / 1000000000000), orderedInterval (-48628082558 / 1000000000000) (-48628082557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1671081098708619 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25844128757 / 1000000000000) (-25844128756 / 1000000000000), orderedInterval (-29225391997 / 1000000000000) (-29225391996 / 1000000000000)))) (orderedInterval (-7646524551 / 1000000000000) (-7646524475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1230910773912547 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27038702296 / 1000000000000) (27038702297 / 1000000000000), orderedInterval (36530453421 / 1000000000000) (36530453422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2109186591301231 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10077059040 / 1000000000000) (10077059041 / 1000000000000), orderedInterval (33243728465 / 1000000000000) (33243728466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1553617296868429 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14567948237 / 1000000000000) (-14567948058 / 1000000000000), orderedInterval (37792295498 / 1000000000000) (37792295677 / 1000000000000)))) (orderedInterval (5107530593 / 1000000000000) (5107530691 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate395_chunkChecks3_1 :
    compactCertificate395.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2383648464014467 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6663191330 / 1000000000000) (-6663191326 / 1000000000000), orderedInterval (32004242840 / 1000000000000) (32004242843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1376200082352043 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29009445187 / 1000000000000) (-29009429300 / 1000000000000), orderedInterval (31804117168 / 1000000000000) (31804133055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2442091196138087 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31136928611 / 1000000000000) (31136946574 / 1000000000000), orderedInterval (-8583317776 / 1000000000000) (-8583299812 / 1000000000000)))) (orderedInterval (73275465558 / 1000000000000) (73275499886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2281718375170403 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17606213949 / 1000000000000) (-17606213340 / 1000000000000), orderedInterval (28406576818 / 1000000000000) (28406577428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1628341896940499 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20212235054 / 1000000000000) (-20212233738 / 1000000000000), orderedInterval (34014736037 / 1000000000000) (34014737353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1846366160868021 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19806944989 / 1000000000000) (-19806944988 / 1000000000000), orderedInterval (-31393024238 / 1000000000000) (-31393024237 / 1000000000000)))) (orderedInterval (-7270927694 / 1000000000000) (-7270926997 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1539307611582949 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29287938049 / 1000000000000) (29287961956 / 1000000000000), orderedInterval (-28260707343 / 1000000000000) (-28260683435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1360024957349929 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43160284277 / 1000000000000) (43160284345 / 1000000000000), orderedInterval (3029197311 / 1000000000000) (3029197379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (394188242158971 / 800000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10292221488 / 1000000000000) (-10292221487 / 1000000000000), orderedInterval (-34429103450 / 1000000000000) (-34429103449 / 1000000000000)))) (orderedInterval (6898347368 / 1000000000000) (6898348295 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate395_chunkChecks3_2 :
    compactCertificate395.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1090345422802337 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2547303107 / 1000000000000) (-2547303105 / 1000000000000), orderedInterval (-48254983418 / 1000000000000) (-48254983417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (924297890154457 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30434651202 / 1000000000000) (-30434642791 / 1000000000000), orderedInterval (42830039580 / 1000000000000) (42830047991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (578382703131571 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50584737542 / 1000000000000) (50584737543 / 1000000000000), orderedInterval (42766184362 / 1000000000000) (42766184363 / 1000000000000)))) (orderedInterval (-6890058796 / 1000000000000) (-6890058426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (311056141358157 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-724715016 / 1000000000000) (-724715009 / 1000000000000), orderedInterval (-90472971832 / 1000000000000) (-90472971825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (844577932825471 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54459051304 / 1000000000000) (-54459051293 / 1000000000000), orderedInterval (-6892027460 / 1000000000000) (-6892027449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1153198962084767 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2732458666 / 1000000000000) (2732458668 / 1000000000000), orderedInterval (46907136811 / 1000000000000) (46907136813 / 1000000000000)))) (orderedInterval (4433867402 / 1000000000000) (4433867432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (487617296868429 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11982578073 / 1000000000000) (-11982578072 / 1000000000000), orderedInterval (-71216200129 / 1000000000000) (-71216200128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1982137240067309 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1869553215 / 1000000000000) (-1869553214 / 1000000000000), orderedInterval (35796009284 / 1000000000000) (35796009286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1323975816070531 / 4000000000000) 3 (IntervalRat.scale (533 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41331619234 / 1000000000000) (-41331610077 / 1000000000000), orderedInterval (14727137385 / 1000000000000) (14727146541 / 1000000000000)))) (orderedInterval (24114205857 / 1000000000000) (24114209396 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate395_chunkChecks3 :
    compactCertificate395.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate395.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate395_chunkChecks3_0
    compactCertificate395_chunkChecks3_1 compactCertificate395_chunkChecks3_2

theorem compactCertificate395_chunkChecks4_0 :
    compactCertificate395.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (533 / 2) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12070845854 / 1000000000000) (-12070845853 / 1000000000000), orderedInterval (-47338893699 / 1000000000000) (-47338893698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (785210775231233 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42134047080 / 1000000000000) (42134119641 / 1000000000000), orderedInterval (-38418833803 / 1000000000000) (-38418761241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (253921031536289 / 800000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34672367234 / 1000000000000) (-34672367233 / 1000000000000), orderedInterval (-28292368143 / 1000000000000) (-28292368142 / 1000000000000)))) (orderedInterval (-8925310496 / 1000000000000) (-8925310261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (229122545868931 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (105258208605 / 1000000000000) (105258208616 / 1000000000000), orderedInterval (4941092224 / 1000000000000) (4941092234 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (615455386956007 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-41947464291 / 1000000000000) (-41947464290 / 1000000000000), orderedInterval (-48628082558 / 1000000000000) (-48628082557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1671081098708619 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25844128757 / 1000000000000) (-25844128756 / 1000000000000), orderedInterval (-29225391997 / 1000000000000) (-29225391996 / 1000000000000)))) (orderedInterval (10979772800 / 1000000000000) (10979772917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1230910773912547 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27038702296 / 1000000000000) (27038702297 / 1000000000000), orderedInterval (36530453421 / 1000000000000) (36530453422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2109186591301231 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10077059040 / 1000000000000) (10077059041 / 1000000000000), orderedInterval (33243728465 / 1000000000000) (33243728466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1553617296868429 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-14567948237 / 1000000000000) (-14567948058 / 1000000000000), orderedInterval (37792295498 / 1000000000000) (37792295677 / 1000000000000)))) (orderedInterval (-6390406360 / 1000000000000) (-6390406183 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate395_chunkChecks4_1 :
    compactCertificate395.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2383648464014467 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6663191330 / 1000000000000) (-6663191326 / 1000000000000), orderedInterval (32004242840 / 1000000000000) (32004242843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1376200082352043 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29009445187 / 1000000000000) (-29009429300 / 1000000000000), orderedInterval (31804117168 / 1000000000000) (31804133055 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2442091196138087 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (31136928611 / 1000000000000) (31136946574 / 1000000000000), orderedInterval (-8583317776 / 1000000000000) (-8583299812 / 1000000000000)))) (orderedInterval (144994112349 / 1000000000000) (144994188503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2281718375170403 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17606213949 / 1000000000000) (-17606213340 / 1000000000000), orderedInterval (28406576818 / 1000000000000) (28406577428 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1628341896940499 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20212235054 / 1000000000000) (-20212233738 / 1000000000000), orderedInterval (34014736037 / 1000000000000) (34014737353 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1846366160868021 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19806944989 / 1000000000000) (-19806944988 / 1000000000000), orderedInterval (-31393024238 / 1000000000000) (-31393024237 / 1000000000000)))) (orderedInterval (-2777694755 / 1000000000000) (-2777693591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1539307611582949 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29287938049 / 1000000000000) (29287961956 / 1000000000000), orderedInterval (-28260707343 / 1000000000000) (-28260683435 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1360024957349929 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43160284277 / 1000000000000) (43160284345 / 1000000000000), orderedInterval (3029197311 / 1000000000000) (3029197379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (394188242158971 / 800000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10292221488 / 1000000000000) (-10292221487 / 1000000000000), orderedInterval (-34429103450 / 1000000000000) (-34429103449 / 1000000000000)))) (orderedInterval (-8204726663 / 1000000000000) (-8204725312 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate395_chunkChecks4_2 :
    compactCertificate395.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1090345422802337 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2547303107 / 1000000000000) (-2547303105 / 1000000000000), orderedInterval (-48254983418 / 1000000000000) (-48254983417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (924297890154457 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30434651202 / 1000000000000) (-30434642791 / 1000000000000), orderedInterval (42830039580 / 1000000000000) (42830047991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (578382703131571 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50584737542 / 1000000000000) (50584737543 / 1000000000000), orderedInterval (42766184362 / 1000000000000) (42766184363 / 1000000000000)))) (orderedInterval (1613839175 / 1000000000000) (1613839504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (311056141358157 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-724715016 / 1000000000000) (-724715009 / 1000000000000), orderedInterval (-90472971832 / 1000000000000) (-90472971825 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (844577932825471 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54459051304 / 1000000000000) (-54459051293 / 1000000000000), orderedInterval (-6892027460 / 1000000000000) (-6892027449 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1153198962084767 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2732458666 / 1000000000000) (2732458668 / 1000000000000), orderedInterval (46907136811 / 1000000000000) (46907136813 / 1000000000000)))) (orderedInterval (166834272 / 1000000000000) (166834303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (487617296868429 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-11982578073 / 1000000000000) (-11982578072 / 1000000000000), orderedInterval (-71216200129 / 1000000000000) (-71216200128 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1982137240067309 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1869553215 / 1000000000000) (-1869553214 / 1000000000000), orderedInterval (35796009284 / 1000000000000) (35796009286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1323975816070531 / 4000000000000) 4 (IntervalRat.scale (533 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41331619234 / 1000000000000) (-41331610077 / 1000000000000), orderedInterval (14727137385 / 1000000000000) (14727146541 / 1000000000000)))) (orderedInterval (20087923069 / 1000000000000) (20087927562 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate395_chunkChecks4 :
    compactCertificate395.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate395.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate395_chunkChecks4_0
    compactCertificate395_chunkChecks4_1 compactCertificate395_chunkChecks4_2

theorem compactCertificate395_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate395.chunkCheck r b = true :=
  compactCertificate395.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate395_chunkChecks0
    · exact compactCertificate395_chunkChecks1
    · exact compactCertificate395_chunkChecks2
    · exact compactCertificate395_chunkChecks3
    · exact compactCertificate395_chunkChecks4)

theorem compactCertificate395_coefficient0 :
    compactCertificate395.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate395_coefficient1 :
    compactCertificate395.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate395_coefficient2 :
    compactCertificate395.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate395_coefficient3 :
    compactCertificate395.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate395_coefficient4 :
    compactCertificate395.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate395_coefficients : ∀ r : Fin 5,
    compactCertificate395.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate395_coefficient0
  · exact compactCertificate395_coefficient1
  · exact compactCertificate395_coefficient2
  · exact compactCertificate395_coefficient3
  · exact compactCertificate395_coefficient4

theorem compactCertificate395_lower : (1 : ℚ) ≤ compactCertificate395.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate395, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate395_proves {t : ℝ} (ht : t ∈ compactCertificate395.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate395.proves compactCertificate395_states compactCertificate395_chunks
    compactCertificate395_coefficients compactCertificate395_lower ht

end Erdos232
