/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate315 : CompactCertificate where
  left := 188
  right := 189
  center := 377 / 2
  grid := fun i =>
    match i.val with
    | 0 => 60
    | 1 => 44
    | 2 => 71
    | 3 => 13
    | 4 => 35
    | 5 => 94
    | 6 => 69
    | 7 => 119
    | 8 => 87
    | 9 => 134
    | 10 => 78
    | 11 => 138
    | 12 => 128
    | 13 => 92
    | 14 => 104
    | 15 => 87
    | 16 => 77
    | 17 => 111
    | 18 => 61
    | 19 => 52
    | 20 => 33
    | 21 => 18
    | 22 => 48
    | 23 => 65
    | 24 => 27
    | 25 => 112
    | _ => 75
  point := fun i =>
    match i.val with
    | 0 => 377 / 2
    | 1 => 555392987358677 / 4000000000000
    | 2 => 179602680842741 / 800000000000
    | 3 => 162062288541439 / 4000000000000
    | 4 => 435322102968883 / 4000000000000
    | 5 => 1181984191769511 / 4000000000000
    | 6 => 870644205938143 / 4000000000000
    | 7 => 1491863686530139 / 4000000000000
    | 8 => 1098900039248401 / 4000000000000
    | 9 => 1685995255034623 / 4000000000000
    | 10 => 973409814346567 / 4000000000000
    | 11 => 1727332797268403 / 4000000000000
    | 12 => 1613898362925407 / 4000000000000
    | 13 => 1151754024665231 / 4000000000000
    | 14 => 1305966308906649 / 4000000000000
    | 15 => 1088778554534281 / 4000000000000
    | 16 => 961968872271901 / 4000000000000
    | 17 => 278816073722199 / 800000000000
    | 18 => 771219933201653 / 4000000000000
    | 19 => 653771678401933 / 4000000000000
    | 20 => 409099960751599 / 4000000000000
    | 21 => 220015319497233 / 4000000000000
    | 22 => 597384391510699 / 4000000000000
    | 23 => 815677314645323 / 4000000000000
    | 24 => 344900039248401 / 4000000000000
    | 25 => 1401999511267121 / 4000000000000
    | _ => 936470699171839 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (41248015525 / 1000000000000) (41248015526 / 1000000000000), orderedInterval (40828278184 / 1000000000000) (40828278185 / 1000000000000))
    | 1 => (orderedInterval (66757672381 / 1000000000000) (66757672384 / 1000000000000), orderedInterval (11090498969 / 1000000000000) (11090498973 / 1000000000000))
    | 2 => (orderedInterval (-41926599967 / 1000000000000) (-41926492941 / 1000000000000), orderedInterval (32923844716 / 1000000000000) (32923951742 / 1000000000000))
    | 3 => (orderedInterval (-55330603928 / 1000000000000) (-55330603927 / 1000000000000), orderedInterval (-111799355327 / 1000000000000) (-111799355326 / 1000000000000))
    | 4 => (orderedInterval (25575694106 / 1000000000000) (25575694876 / 1000000000000), orderedInterval (-72197838970 / 1000000000000) (-72197838200 / 1000000000000))
    | 5 => (orderedInterval (38321995852 / 1000000000000) (38321995853 / 1000000000000), orderedInterval (26123588465 / 1000000000000) (26123588466 / 1000000000000))
    | 6 => (orderedInterval (-53782644163 / 1000000000000) (-53782643837 / 1000000000000), orderedInterval (5801695611 / 1000000000000) (5801695937 / 1000000000000))
    | 7 => (orderedInterval (4064618107 / 1000000000000) (4064618111 / 1000000000000), orderedInterval (-41119823096 / 1000000000000) (-41119823092 / 1000000000000))
    | 8 => (orderedInterval (-39162085275 / 1000000000000) (-39161993471 / 1000000000000), orderedInterval (28064646400 / 1000000000000) (28064738204 / 1000000000000))
    | 9 => (orderedInterval (37554316918 / 1000000000000) (37554316925 / 1000000000000), orderedInterval (9957641455 / 1000000000000) (9957641463 / 1000000000000))
    | 10 => (orderedInterval (-40283089624 / 1000000000000) (-40282978804 / 1000000000000), orderedInterval (31599621171 / 1000000000000) (31599731992 / 1000000000000))
    | 11 => (orderedInterval (-30582009955 / 1000000000000) (-30581954231 / 1000000000000), orderedInterval (23251068581 / 1000000000000) (23251124305 / 1000000000000))
    | 12 => (orderedInterval (33548259358 / 1000000000000) (33548358844 / 1000000000000), orderedInterval (-21310234946 / 1000000000000) (-21310135459 / 1000000000000))
    | 13 => (orderedInterval (-14032710744 / 1000000000000) (-14032710596 / 1000000000000), orderedInterval (44902459779 / 1000000000000) (44902459926 / 1000000000000))
    | 14 => (orderedInterval (23116525575 / 1000000000000) (23116525576 / 1000000000000), orderedInterval (37587841879 / 1000000000000) (37587841880 / 1000000000000))
    | 15 => (orderedInterval (16081578279 / 1000000000000) (16081578545 / 1000000000000), orderedInterval (-45639036810 / 1000000000000) (-45639036544 / 1000000000000))
    | 16 => (orderedInterval (30125944056 / 1000000000000) (30125952661 / 1000000000000), orderedInterval (-41770938433 / 1000000000000) (-41770929828 / 1000000000000))
    | 17 => (orderedInterval (-23719667099 / 1000000000000) (-23719667098 / 1000000000000), orderedInterval (-35518964279 / 1000000000000) (-35518964278 / 1000000000000))
    | 18 => (orderedInterval (-53324735836 / 1000000000000) (-53324729014 / 1000000000000), orderedInterval (21547376258 / 1000000000000) (21547383080 / 1000000000000))
    | 19 => (orderedInterval (47489423671 / 1000000000000) (47489423672 / 1000000000000), orderedInterval (40349296743 / 1000000000000) (40349296744 / 1000000000000))
    | 20 => (orderedInterval (45415756736 / 1000000000000) (45415771879 / 1000000000000), orderedInterval (-64735767142 / 1000000000000) (-64735751999 / 1000000000000))
    | 21 => (orderedInterval (-74248112490 / 1000000000000) (-74248040631 / 1000000000000), orderedInterval (78529477418 / 1000000000000) (78529549277 / 1000000000000))
    | 22 => (orderedInterval (-40327846147 / 1000000000000) (-40327826186 / 1000000000000), orderedInterval (51480749649 / 1000000000000) (51480769610 / 1000000000000))
    | 23 => (orderedInterval (-26816442432 / 1000000000000) (-26816442431 / 1000000000000), orderedInterval (-48952644275 / 1000000000000) (-48952644274 / 1000000000000))
    | 24 => (orderedInterval (-70173362993 / 1000000000000) (-70173324526 / 1000000000000), orderedInterval (49994165109 / 1000000000000) (49994203575 / 1000000000000))
    | 25 => (orderedInterval (-23122121719 / 1000000000000) (-23122118952 / 1000000000000), orderedInterval (35833651108 / 1000000000000) (35833653874 / 1000000000000))
    | _ => (orderedInterval (34263073242 / 1000000000000) (34263094855 / 1000000000000), orderedInterval (-39383129722 / 1000000000000) (-39383108110 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14511020692 / 1000000000000) (14511026987 / 1000000000000)
      | 1 => orderedInterval (-1190185869 / 1000000000000) (-1190185818 / 1000000000000)
      | 2 => orderedInterval (-1071839425 / 1000000000000) (-1071837195 / 1000000000000)
      | 3 => orderedInterval (-14005007080 / 1000000000000) (-14004990871 / 1000000000000)
      | 4 => orderedInterval (-2049607699 / 1000000000000) (-2049605866 / 1000000000000)
      | 5 => orderedInterval (-2145620583 / 1000000000000) (-2145620069 / 1000000000000)
      | 6 => orderedInterval (7316844095 / 1000000000000) (7316845727 / 1000000000000)
      | 7 => orderedInterval (4341092418 / 1000000000000) (4341094221 / 1000000000000)
      | _ => orderedInterval (-4969511997 / 1000000000000) (-4969507431 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18560042274 / 1000000000000) (18560049770 / 1000000000000)
      | 1 => orderedInterval (-4172478935 / 1000000000000) (-4172478892 / 1000000000000)
      | 2 => orderedInterval (3497981807 / 1000000000000) (3497985060 / 1000000000000)
      | 3 => orderedInterval (6638208374 / 1000000000000) (6638237280 / 1000000000000)
      | 4 => orderedInterval (6980028920 / 1000000000000) (6980032822 / 1000000000000)
      | 5 => orderedInterval (607262343 / 1000000000000) (607263003 / 1000000000000)
      | 6 => orderedInterval (-6647604015 / 1000000000000) (-6647602588 / 1000000000000)
      | 7 => orderedInterval (2710098452 / 1000000000000) (2710099219 / 1000000000000)
      | _ => orderedInterval (3891643682 / 1000000000000) (3891649317 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13295363515 / 1000000000000) (-13295354548 / 1000000000000)
      | 1 => orderedInterval (6377892741 / 1000000000000) (6377892786 / 1000000000000)
      | 2 => orderedInterval (2482631756 / 1000000000000) (2482636520 / 1000000000000)
      | 3 => orderedInterval (61119919251 / 1000000000000) (61119975000 / 1000000000000)
      | 4 => orderedInterval (6184986870 / 1000000000000) (6184995213 / 1000000000000)
      | 5 => orderedInterval (4491857472 / 1000000000000) (4491858323 / 1000000000000)
      | 6 => orderedInterval (-7299308397 / 1000000000000) (-7299307060 / 1000000000000)
      | 7 => orderedInterval (-3110581585 / 1000000000000) (-3110581162 / 1000000000000)
      | _ => orderedInterval (3477041248 / 1000000000000) (3477048469 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19417107463 / 1000000000000) (-19417096785 / 1000000000000)
      | 1 => orderedInterval (7615499523 / 1000000000000) (7615499583 / 1000000000000)
      | 2 => orderedInterval (-11936956505 / 1000000000000) (-11936949551 / 1000000000000)
      | 3 => orderedInterval (-25319266677 / 1000000000000) (-25319152735 / 1000000000000)
      | 4 => orderedInterval (-17951016909 / 1000000000000) (-17950999100 / 1000000000000)
      | 5 => orderedInterval (2346920387 / 1000000000000) (2346921484 / 1000000000000)
      | 6 => orderedInterval (5550631675 / 1000000000000) (5550632969 / 1000000000000)
      | 7 => orderedInterval (-4116243030 / 1000000000000) (-4116242748 / 1000000000000)
      | _ => orderedInterval (4548057863 / 1000000000000) (4548067307 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11787703161 / 1000000000000) (11787715934 / 1000000000000)
      | 1 => orderedInterval (-16427470229 / 1000000000000) (-16427470143 / 1000000000000)
      | 2 => orderedInterval (-6064956382 / 1000000000000) (-6064946186 / 1000000000000)
      | 3 => orderedInterval (-294586890402 / 1000000000000) (-294586646569 / 1000000000000)
      | 4 => orderedInterval (-20799669687 / 1000000000000) (-20799631547 / 1000000000000)
      | 5 => orderedInterval (-10882174227 / 1000000000000) (-10882172803 / 1000000000000)
      | 6 => orderedInterval (7881979291 / 1000000000000) (7881980581 / 1000000000000)
      | 7 => orderedInterval (3228769354 / 1000000000000) (3228769568 / 1000000000000)
      | _ => orderedInterval (7135337675 / 1000000000000) (7135350394 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (737184552 / 1000000000000) (737219685 / 1000000000000)
    | 1 => orderedInterval (32065182902 / 1000000000000) (32065234991 / 1000000000000)
    | 2 => orderedInterval (60429075841 / 1000000000000) (60429163541 / 1000000000000)
    | 3 => orderedInterval (-58679481136 / 1000000000000) (-58679319576 / 1000000000000)
    | _ => orderedInterval (-318727371446 / 1000000000000) (-318727050771 / 1000000000000)

theorem compactCertificate315_stateChecks0 :
    compactCertificate315.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (377 / 2)) (orderedInterval (41248015525 / 1000000000000) (41248015526 / 1000000000000), orderedInterval (40828278184 / 1000000000000) (40828278185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (555392987358677 / 4000000000000)) (orderedInterval (66757672381 / 1000000000000) (66757672384 / 1000000000000), orderedInterval (11090498969 / 1000000000000) (11090498973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (179602680842741 / 800000000000)) (orderedInterval (-41926599967 / 1000000000000) (-41926492941 / 1000000000000), orderedInterval (32923844716 / 1000000000000) (32923951742 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks1 :
    compactCertificate315.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (162062288541439 / 4000000000000)) (orderedInterval (-55330603928 / 1000000000000) (-55330603927 / 1000000000000), orderedInterval (-111799355327 / 1000000000000) (-111799355326 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (435322102968883 / 4000000000000)) (orderedInterval (25575694106 / 1000000000000) (25575694876 / 1000000000000), orderedInterval (-72197838970 / 1000000000000) (-72197838200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1181984191769511 / 4000000000000)) (orderedInterval (38321995852 / 1000000000000) (38321995853 / 1000000000000), orderedInterval (26123588465 / 1000000000000) (26123588466 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks2 :
    compactCertificate315.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (870644205938143 / 4000000000000)) (orderedInterval (-53782644163 / 1000000000000) (-53782643837 / 1000000000000), orderedInterval (5801695611 / 1000000000000) (5801695937 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1491863686530139 / 4000000000000)) (orderedInterval (4064618107 / 1000000000000) (4064618111 / 1000000000000), orderedInterval (-41119823096 / 1000000000000) (-41119823092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1098900039248401 / 4000000000000)) (orderedInterval (-39162085275 / 1000000000000) (-39161993471 / 1000000000000), orderedInterval (28064646400 / 1000000000000) (28064738204 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks3 :
    compactCertificate315.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1685995255034623 / 4000000000000)) (orderedInterval (37554316918 / 1000000000000) (37554316925 / 1000000000000), orderedInterval (9957641455 / 1000000000000) (9957641463 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (973409814346567 / 4000000000000)) (orderedInterval (-40283089624 / 1000000000000) (-40282978804 / 1000000000000), orderedInterval (31599621171 / 1000000000000) (31599731992 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1727332797268403 / 4000000000000)) (orderedInterval (-30582009955 / 1000000000000) (-30581954231 / 1000000000000), orderedInterval (23251068581 / 1000000000000) (23251124305 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks4 :
    compactCertificate315.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1613898362925407 / 4000000000000)) (orderedInterval (33548259358 / 1000000000000) (33548358844 / 1000000000000), orderedInterval (-21310234946 / 1000000000000) (-21310135459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1151754024665231 / 4000000000000)) (orderedInterval (-14032710744 / 1000000000000) (-14032710596 / 1000000000000), orderedInterval (44902459779 / 1000000000000) (44902459926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1305966308906649 / 4000000000000)) (orderedInterval (23116525575 / 1000000000000) (23116525576 / 1000000000000), orderedInterval (37587841879 / 1000000000000) (37587841880 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks5 :
    compactCertificate315.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1088778554534281 / 4000000000000)) (orderedInterval (16081578279 / 1000000000000) (16081578545 / 1000000000000), orderedInterval (-45639036810 / 1000000000000) (-45639036544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (961968872271901 / 4000000000000)) (orderedInterval (30125944056 / 1000000000000) (30125952661 / 1000000000000), orderedInterval (-41770938433 / 1000000000000) (-41770929828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (278816073722199 / 800000000000)) (orderedInterval (-23719667099 / 1000000000000) (-23719667098 / 1000000000000), orderedInterval (-35518964279 / 1000000000000) (-35518964278 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks6 :
    compactCertificate315.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (771219933201653 / 4000000000000)) (orderedInterval (-53324735836 / 1000000000000) (-53324729014 / 1000000000000), orderedInterval (21547376258 / 1000000000000) (21547383080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (653771678401933 / 4000000000000)) (orderedInterval (47489423671 / 1000000000000) (47489423672 / 1000000000000), orderedInterval (40349296743 / 1000000000000) (40349296744 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (409099960751599 / 4000000000000)) (orderedInterval (45415756736 / 1000000000000) (45415771879 / 1000000000000), orderedInterval (-64735767142 / 1000000000000) (-64735751999 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks7 :
    compactCertificate315.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (220015319497233 / 4000000000000)) (orderedInterval (-74248112490 / 1000000000000) (-74248040631 / 1000000000000), orderedInterval (78529477418 / 1000000000000) (78529549277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (597384391510699 / 4000000000000)) (orderedInterval (-40327846147 / 1000000000000) (-40327826186 / 1000000000000), orderedInterval (51480749649 / 1000000000000) (51480769610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (815677314645323 / 4000000000000)) (orderedInterval (-26816442432 / 1000000000000) (-26816442431 / 1000000000000), orderedInterval (-48952644275 / 1000000000000) (-48952644274 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_stateChecks8 :
    compactCertificate315.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (344900039248401 / 4000000000000)) (orderedInterval (-70173362993 / 1000000000000) (-70173324526 / 1000000000000), orderedInterval (49994165109 / 1000000000000) (49994203575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1401999511267121 / 4000000000000)) (orderedInterval (-23122121719 / 1000000000000) (-23122118952 / 1000000000000), orderedInterval (35833651108 / 1000000000000) (35833653874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (936470699171839 / 4000000000000)) (orderedInterval (34263073242 / 1000000000000) (34263094855 / 1000000000000), orderedInterval (-39383129722 / 1000000000000) (-39383108110 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_states : ∀ j,
    BesselStateValid (compactCertificate315.point j) (compactCertificate315.state j) :=
  compactCertificate315.statesValid_of_checks3 compactCertificate315_stateChecks0
    compactCertificate315_stateChecks1 compactCertificate315_stateChecks2
    compactCertificate315_stateChecks3 compactCertificate315_stateChecks4
    compactCertificate315_stateChecks5 compactCertificate315_stateChecks6
    compactCertificate315_stateChecks7 compactCertificate315_stateChecks8

theorem compactCertificate315_chunkChecks0_0 :
    compactCertificate315.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (377 / 2) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41248015525 / 1000000000000) (41248015526 / 1000000000000), orderedInterval (40828278184 / 1000000000000) (40828278185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (555392987358677 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (66757672381 / 1000000000000) (66757672384 / 1000000000000), orderedInterval (11090498969 / 1000000000000) (11090498973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (179602680842741 / 800000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41926599967 / 1000000000000) (-41926492941 / 1000000000000), orderedInterval (32923844716 / 1000000000000) (32923951742 / 1000000000000)))) (orderedInterval (14511020692 / 1000000000000) (14511026987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (162062288541439 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55330603928 / 1000000000000) (-55330603927 / 1000000000000), orderedInterval (-111799355327 / 1000000000000) (-111799355326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (435322102968883 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25575694106 / 1000000000000) (25575694876 / 1000000000000), orderedInterval (-72197838970 / 1000000000000) (-72197838200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1181984191769511 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (38321995852 / 1000000000000) (38321995853 / 1000000000000), orderedInterval (26123588465 / 1000000000000) (26123588466 / 1000000000000)))) (orderedInterval (-1190185869 / 1000000000000) (-1190185818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (870644205938143 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53782644163 / 1000000000000) (-53782643837 / 1000000000000), orderedInterval (5801695611 / 1000000000000) (5801695937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1491863686530139 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4064618107 / 1000000000000) (4064618111 / 1000000000000), orderedInterval (-41119823096 / 1000000000000) (-41119823092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1098900039248401 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39162085275 / 1000000000000) (-39161993471 / 1000000000000), orderedInterval (28064646400 / 1000000000000) (28064738204 / 1000000000000)))) (orderedInterval (-1071839425 / 1000000000000) (-1071837195 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks0_1 :
    compactCertificate315.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1685995255034623 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37554316918 / 1000000000000) (37554316925 / 1000000000000), orderedInterval (9957641455 / 1000000000000) (9957641463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (973409814346567 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40283089624 / 1000000000000) (-40282978804 / 1000000000000), orderedInterval (31599621171 / 1000000000000) (31599731992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1727332797268403 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30582009955 / 1000000000000) (-30581954231 / 1000000000000), orderedInterval (23251068581 / 1000000000000) (23251124305 / 1000000000000)))) (orderedInterval (-14005007080 / 1000000000000) (-14004990871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1613898362925407 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33548259358 / 1000000000000) (33548358844 / 1000000000000), orderedInterval (-21310234946 / 1000000000000) (-21310135459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1151754024665231 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14032710744 / 1000000000000) (-14032710596 / 1000000000000), orderedInterval (44902459779 / 1000000000000) (44902459926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1305966308906649 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23116525575 / 1000000000000) (23116525576 / 1000000000000), orderedInterval (37587841879 / 1000000000000) (37587841880 / 1000000000000)))) (orderedInterval (-2049607699 / 1000000000000) (-2049605866 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1088778554534281 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16081578279 / 1000000000000) (16081578545 / 1000000000000), orderedInterval (-45639036810 / 1000000000000) (-45639036544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (961968872271901 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30125944056 / 1000000000000) (30125952661 / 1000000000000), orderedInterval (-41770938433 / 1000000000000) (-41770929828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (278816073722199 / 800000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23719667099 / 1000000000000) (-23719667098 / 1000000000000), orderedInterval (-35518964279 / 1000000000000) (-35518964278 / 1000000000000)))) (orderedInterval (-2145620583 / 1000000000000) (-2145620069 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks0_2 :
    compactCertificate315.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (771219933201653 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53324735836 / 1000000000000) (-53324729014 / 1000000000000), orderedInterval (21547376258 / 1000000000000) (21547383080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (653771678401933 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47489423671 / 1000000000000) (47489423672 / 1000000000000), orderedInterval (40349296743 / 1000000000000) (40349296744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (409099960751599 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45415756736 / 1000000000000) (45415771879 / 1000000000000), orderedInterval (-64735767142 / 1000000000000) (-64735751999 / 1000000000000)))) (orderedInterval (7316844095 / 1000000000000) (7316845727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (220015319497233 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74248112490 / 1000000000000) (-74248040631 / 1000000000000), orderedInterval (78529477418 / 1000000000000) (78529549277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (597384391510699 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40327846147 / 1000000000000) (-40327826186 / 1000000000000), orderedInterval (51480749649 / 1000000000000) (51480769610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (815677314645323 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26816442432 / 1000000000000) (-26816442431 / 1000000000000), orderedInterval (-48952644275 / 1000000000000) (-48952644274 / 1000000000000)))) (orderedInterval (4341092418 / 1000000000000) (4341094221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (344900039248401 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70173362993 / 1000000000000) (-70173324526 / 1000000000000), orderedInterval (49994165109 / 1000000000000) (49994203575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1401999511267121 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23122121719 / 1000000000000) (-23122118952 / 1000000000000), orderedInterval (35833651108 / 1000000000000) (35833653874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (936470699171839 / 4000000000000) 0 (IntervalRat.scale (377 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34263073242 / 1000000000000) (34263094855 / 1000000000000), orderedInterval (-39383129722 / 1000000000000) (-39383108110 / 1000000000000)))) (orderedInterval (-4969511997 / 1000000000000) (-4969507431 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks0 :
    compactCertificate315.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate315.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate315_chunkChecks0_0
    compactCertificate315_chunkChecks0_1 compactCertificate315_chunkChecks0_2

theorem compactCertificate315_chunkChecks1_0 :
    compactCertificate315.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (377 / 2) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41248015525 / 1000000000000) (41248015526 / 1000000000000), orderedInterval (40828278184 / 1000000000000) (40828278185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (555392987358677 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (66757672381 / 1000000000000) (66757672384 / 1000000000000), orderedInterval (11090498969 / 1000000000000) (11090498973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (179602680842741 / 800000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41926599967 / 1000000000000) (-41926492941 / 1000000000000), orderedInterval (32923844716 / 1000000000000) (32923951742 / 1000000000000)))) (orderedInterval (18560042274 / 1000000000000) (18560049770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (162062288541439 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55330603928 / 1000000000000) (-55330603927 / 1000000000000), orderedInterval (-111799355327 / 1000000000000) (-111799355326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (435322102968883 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25575694106 / 1000000000000) (25575694876 / 1000000000000), orderedInterval (-72197838970 / 1000000000000) (-72197838200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1181984191769511 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (38321995852 / 1000000000000) (38321995853 / 1000000000000), orderedInterval (26123588465 / 1000000000000) (26123588466 / 1000000000000)))) (orderedInterval (-4172478935 / 1000000000000) (-4172478892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (870644205938143 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53782644163 / 1000000000000) (-53782643837 / 1000000000000), orderedInterval (5801695611 / 1000000000000) (5801695937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1491863686530139 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4064618107 / 1000000000000) (4064618111 / 1000000000000), orderedInterval (-41119823096 / 1000000000000) (-41119823092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1098900039248401 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39162085275 / 1000000000000) (-39161993471 / 1000000000000), orderedInterval (28064646400 / 1000000000000) (28064738204 / 1000000000000)))) (orderedInterval (3497981807 / 1000000000000) (3497985060 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks1_1 :
    compactCertificate315.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1685995255034623 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37554316918 / 1000000000000) (37554316925 / 1000000000000), orderedInterval (9957641455 / 1000000000000) (9957641463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (973409814346567 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40283089624 / 1000000000000) (-40282978804 / 1000000000000), orderedInterval (31599621171 / 1000000000000) (31599731992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1727332797268403 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30582009955 / 1000000000000) (-30581954231 / 1000000000000), orderedInterval (23251068581 / 1000000000000) (23251124305 / 1000000000000)))) (orderedInterval (6638208374 / 1000000000000) (6638237280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1613898362925407 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33548259358 / 1000000000000) (33548358844 / 1000000000000), orderedInterval (-21310234946 / 1000000000000) (-21310135459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1151754024665231 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14032710744 / 1000000000000) (-14032710596 / 1000000000000), orderedInterval (44902459779 / 1000000000000) (44902459926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1305966308906649 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23116525575 / 1000000000000) (23116525576 / 1000000000000), orderedInterval (37587841879 / 1000000000000) (37587841880 / 1000000000000)))) (orderedInterval (6980028920 / 1000000000000) (6980032822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1088778554534281 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16081578279 / 1000000000000) (16081578545 / 1000000000000), orderedInterval (-45639036810 / 1000000000000) (-45639036544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (961968872271901 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30125944056 / 1000000000000) (30125952661 / 1000000000000), orderedInterval (-41770938433 / 1000000000000) (-41770929828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (278816073722199 / 800000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23719667099 / 1000000000000) (-23719667098 / 1000000000000), orderedInterval (-35518964279 / 1000000000000) (-35518964278 / 1000000000000)))) (orderedInterval (607262343 / 1000000000000) (607263003 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks1_2 :
    compactCertificate315.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (771219933201653 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53324735836 / 1000000000000) (-53324729014 / 1000000000000), orderedInterval (21547376258 / 1000000000000) (21547383080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (653771678401933 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47489423671 / 1000000000000) (47489423672 / 1000000000000), orderedInterval (40349296743 / 1000000000000) (40349296744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (409099960751599 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45415756736 / 1000000000000) (45415771879 / 1000000000000), orderedInterval (-64735767142 / 1000000000000) (-64735751999 / 1000000000000)))) (orderedInterval (-6647604015 / 1000000000000) (-6647602588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (220015319497233 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74248112490 / 1000000000000) (-74248040631 / 1000000000000), orderedInterval (78529477418 / 1000000000000) (78529549277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (597384391510699 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40327846147 / 1000000000000) (-40327826186 / 1000000000000), orderedInterval (51480749649 / 1000000000000) (51480769610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (815677314645323 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26816442432 / 1000000000000) (-26816442431 / 1000000000000), orderedInterval (-48952644275 / 1000000000000) (-48952644274 / 1000000000000)))) (orderedInterval (2710098452 / 1000000000000) (2710099219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (344900039248401 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70173362993 / 1000000000000) (-70173324526 / 1000000000000), orderedInterval (49994165109 / 1000000000000) (49994203575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1401999511267121 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23122121719 / 1000000000000) (-23122118952 / 1000000000000), orderedInterval (35833651108 / 1000000000000) (35833653874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (936470699171839 / 4000000000000) 1 (IntervalRat.scale (377 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34263073242 / 1000000000000) (34263094855 / 1000000000000), orderedInterval (-39383129722 / 1000000000000) (-39383108110 / 1000000000000)))) (orderedInterval (3891643682 / 1000000000000) (3891649317 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks1 :
    compactCertificate315.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate315.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate315_chunkChecks1_0
    compactCertificate315_chunkChecks1_1 compactCertificate315_chunkChecks1_2

theorem compactCertificate315_chunkChecks2_0 :
    compactCertificate315.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (377 / 2) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41248015525 / 1000000000000) (41248015526 / 1000000000000), orderedInterval (40828278184 / 1000000000000) (40828278185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (555392987358677 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (66757672381 / 1000000000000) (66757672384 / 1000000000000), orderedInterval (11090498969 / 1000000000000) (11090498973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (179602680842741 / 800000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41926599967 / 1000000000000) (-41926492941 / 1000000000000), orderedInterval (32923844716 / 1000000000000) (32923951742 / 1000000000000)))) (orderedInterval (-13295363515 / 1000000000000) (-13295354548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (162062288541439 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55330603928 / 1000000000000) (-55330603927 / 1000000000000), orderedInterval (-111799355327 / 1000000000000) (-111799355326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (435322102968883 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25575694106 / 1000000000000) (25575694876 / 1000000000000), orderedInterval (-72197838970 / 1000000000000) (-72197838200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1181984191769511 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (38321995852 / 1000000000000) (38321995853 / 1000000000000), orderedInterval (26123588465 / 1000000000000) (26123588466 / 1000000000000)))) (orderedInterval (6377892741 / 1000000000000) (6377892786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (870644205938143 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53782644163 / 1000000000000) (-53782643837 / 1000000000000), orderedInterval (5801695611 / 1000000000000) (5801695937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1491863686530139 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4064618107 / 1000000000000) (4064618111 / 1000000000000), orderedInterval (-41119823096 / 1000000000000) (-41119823092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1098900039248401 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39162085275 / 1000000000000) (-39161993471 / 1000000000000), orderedInterval (28064646400 / 1000000000000) (28064738204 / 1000000000000)))) (orderedInterval (2482631756 / 1000000000000) (2482636520 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks2_1 :
    compactCertificate315.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1685995255034623 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37554316918 / 1000000000000) (37554316925 / 1000000000000), orderedInterval (9957641455 / 1000000000000) (9957641463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (973409814346567 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40283089624 / 1000000000000) (-40282978804 / 1000000000000), orderedInterval (31599621171 / 1000000000000) (31599731992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1727332797268403 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30582009955 / 1000000000000) (-30581954231 / 1000000000000), orderedInterval (23251068581 / 1000000000000) (23251124305 / 1000000000000)))) (orderedInterval (61119919251 / 1000000000000) (61119975000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1613898362925407 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33548259358 / 1000000000000) (33548358844 / 1000000000000), orderedInterval (-21310234946 / 1000000000000) (-21310135459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1151754024665231 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14032710744 / 1000000000000) (-14032710596 / 1000000000000), orderedInterval (44902459779 / 1000000000000) (44902459926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1305966308906649 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23116525575 / 1000000000000) (23116525576 / 1000000000000), orderedInterval (37587841879 / 1000000000000) (37587841880 / 1000000000000)))) (orderedInterval (6184986870 / 1000000000000) (6184995213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1088778554534281 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16081578279 / 1000000000000) (16081578545 / 1000000000000), orderedInterval (-45639036810 / 1000000000000) (-45639036544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (961968872271901 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30125944056 / 1000000000000) (30125952661 / 1000000000000), orderedInterval (-41770938433 / 1000000000000) (-41770929828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (278816073722199 / 800000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23719667099 / 1000000000000) (-23719667098 / 1000000000000), orderedInterval (-35518964279 / 1000000000000) (-35518964278 / 1000000000000)))) (orderedInterval (4491857472 / 1000000000000) (4491858323 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks2_2 :
    compactCertificate315.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (771219933201653 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53324735836 / 1000000000000) (-53324729014 / 1000000000000), orderedInterval (21547376258 / 1000000000000) (21547383080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (653771678401933 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47489423671 / 1000000000000) (47489423672 / 1000000000000), orderedInterval (40349296743 / 1000000000000) (40349296744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (409099960751599 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45415756736 / 1000000000000) (45415771879 / 1000000000000), orderedInterval (-64735767142 / 1000000000000) (-64735751999 / 1000000000000)))) (orderedInterval (-7299308397 / 1000000000000) (-7299307060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (220015319497233 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74248112490 / 1000000000000) (-74248040631 / 1000000000000), orderedInterval (78529477418 / 1000000000000) (78529549277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (597384391510699 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40327846147 / 1000000000000) (-40327826186 / 1000000000000), orderedInterval (51480749649 / 1000000000000) (51480769610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (815677314645323 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26816442432 / 1000000000000) (-26816442431 / 1000000000000), orderedInterval (-48952644275 / 1000000000000) (-48952644274 / 1000000000000)))) (orderedInterval (-3110581585 / 1000000000000) (-3110581162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (344900039248401 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70173362993 / 1000000000000) (-70173324526 / 1000000000000), orderedInterval (49994165109 / 1000000000000) (49994203575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1401999511267121 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23122121719 / 1000000000000) (-23122118952 / 1000000000000), orderedInterval (35833651108 / 1000000000000) (35833653874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (936470699171839 / 4000000000000) 2 (IntervalRat.scale (377 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34263073242 / 1000000000000) (34263094855 / 1000000000000), orderedInterval (-39383129722 / 1000000000000) (-39383108110 / 1000000000000)))) (orderedInterval (3477041248 / 1000000000000) (3477048469 / 1000000000000))) = true
  rfl'

theorem compactCertificate315_chunkChecks2 :
    compactCertificate315.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate315.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate315_chunkChecks2_0
    compactCertificate315_chunkChecks2_1 compactCertificate315_chunkChecks2_2

theorem compactCertificate315_chunkChecks3_0 :
    compactCertificate315.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (377 / 2) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41248015525 / 1000000000000) (41248015526 / 1000000000000), orderedInterval (40828278184 / 1000000000000) (40828278185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (555392987358677 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (66757672381 / 1000000000000) (66757672384 / 1000000000000), orderedInterval (11090498969 / 1000000000000) (11090498973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (179602680842741 / 800000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41926599967 / 1000000000000) (-41926492941 / 1000000000000), orderedInterval (32923844716 / 1000000000000) (32923951742 / 1000000000000)))) (orderedInterval (-19417107463 / 1000000000000) (-19417096785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (162062288541439 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55330603928 / 1000000000000) (-55330603927 / 1000000000000), orderedInterval (-111799355327 / 1000000000000) (-111799355326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (435322102968883 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25575694106 / 1000000000000) (25575694876 / 1000000000000), orderedInterval (-72197838970 / 1000000000000) (-72197838200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1181984191769511 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (38321995852 / 1000000000000) (38321995853 / 1000000000000), orderedInterval (26123588465 / 1000000000000) (26123588466 / 1000000000000)))) (orderedInterval (7615499523 / 1000000000000) (7615499583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (870644205938143 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53782644163 / 1000000000000) (-53782643837 / 1000000000000), orderedInterval (5801695611 / 1000000000000) (5801695937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1491863686530139 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4064618107 / 1000000000000) (4064618111 / 1000000000000), orderedInterval (-41119823096 / 1000000000000) (-41119823092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1098900039248401 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39162085275 / 1000000000000) (-39161993471 / 1000000000000), orderedInterval (28064646400 / 1000000000000) (28064738204 / 1000000000000)))) (orderedInterval (-11936956505 / 1000000000000) (-11936949551 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate315_chunkChecks3_1 :
    compactCertificate315.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1685995255034623 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37554316918 / 1000000000000) (37554316925 / 1000000000000), orderedInterval (9957641455 / 1000000000000) (9957641463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (973409814346567 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40283089624 / 1000000000000) (-40282978804 / 1000000000000), orderedInterval (31599621171 / 1000000000000) (31599731992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1727332797268403 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30582009955 / 1000000000000) (-30581954231 / 1000000000000), orderedInterval (23251068581 / 1000000000000) (23251124305 / 1000000000000)))) (orderedInterval (-25319266677 / 1000000000000) (-25319152735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1613898362925407 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33548259358 / 1000000000000) (33548358844 / 1000000000000), orderedInterval (-21310234946 / 1000000000000) (-21310135459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1151754024665231 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14032710744 / 1000000000000) (-14032710596 / 1000000000000), orderedInterval (44902459779 / 1000000000000) (44902459926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1305966308906649 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23116525575 / 1000000000000) (23116525576 / 1000000000000), orderedInterval (37587841879 / 1000000000000) (37587841880 / 1000000000000)))) (orderedInterval (-17951016909 / 1000000000000) (-17950999100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1088778554534281 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16081578279 / 1000000000000) (16081578545 / 1000000000000), orderedInterval (-45639036810 / 1000000000000) (-45639036544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (961968872271901 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30125944056 / 1000000000000) (30125952661 / 1000000000000), orderedInterval (-41770938433 / 1000000000000) (-41770929828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (278816073722199 / 800000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23719667099 / 1000000000000) (-23719667098 / 1000000000000), orderedInterval (-35518964279 / 1000000000000) (-35518964278 / 1000000000000)))) (orderedInterval (2346920387 / 1000000000000) (2346921484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate315_chunkChecks3_2 :
    compactCertificate315.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (771219933201653 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53324735836 / 1000000000000) (-53324729014 / 1000000000000), orderedInterval (21547376258 / 1000000000000) (21547383080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (653771678401933 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47489423671 / 1000000000000) (47489423672 / 1000000000000), orderedInterval (40349296743 / 1000000000000) (40349296744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (409099960751599 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45415756736 / 1000000000000) (45415771879 / 1000000000000), orderedInterval (-64735767142 / 1000000000000) (-64735751999 / 1000000000000)))) (orderedInterval (5550631675 / 1000000000000) (5550632969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (220015319497233 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74248112490 / 1000000000000) (-74248040631 / 1000000000000), orderedInterval (78529477418 / 1000000000000) (78529549277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (597384391510699 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40327846147 / 1000000000000) (-40327826186 / 1000000000000), orderedInterval (51480749649 / 1000000000000) (51480769610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (815677314645323 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26816442432 / 1000000000000) (-26816442431 / 1000000000000), orderedInterval (-48952644275 / 1000000000000) (-48952644274 / 1000000000000)))) (orderedInterval (-4116243030 / 1000000000000) (-4116242748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (344900039248401 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70173362993 / 1000000000000) (-70173324526 / 1000000000000), orderedInterval (49994165109 / 1000000000000) (49994203575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1401999511267121 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23122121719 / 1000000000000) (-23122118952 / 1000000000000), orderedInterval (35833651108 / 1000000000000) (35833653874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (936470699171839 / 4000000000000) 3 (IntervalRat.scale (377 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34263073242 / 1000000000000) (34263094855 / 1000000000000), orderedInterval (-39383129722 / 1000000000000) (-39383108110 / 1000000000000)))) (orderedInterval (4548057863 / 1000000000000) (4548067307 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate315_chunkChecks3 :
    compactCertificate315.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate315.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate315_chunkChecks3_0
    compactCertificate315_chunkChecks3_1 compactCertificate315_chunkChecks3_2

theorem compactCertificate315_chunkChecks4_0 :
    compactCertificate315.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (377 / 2) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41248015525 / 1000000000000) (41248015526 / 1000000000000), orderedInterval (40828278184 / 1000000000000) (40828278185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (555392987358677 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (66757672381 / 1000000000000) (66757672384 / 1000000000000), orderedInterval (11090498969 / 1000000000000) (11090498973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (179602680842741 / 800000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-41926599967 / 1000000000000) (-41926492941 / 1000000000000), orderedInterval (32923844716 / 1000000000000) (32923951742 / 1000000000000)))) (orderedInterval (11787703161 / 1000000000000) (11787715934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (162062288541439 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55330603928 / 1000000000000) (-55330603927 / 1000000000000), orderedInterval (-111799355327 / 1000000000000) (-111799355326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (435322102968883 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25575694106 / 1000000000000) (25575694876 / 1000000000000), orderedInterval (-72197838970 / 1000000000000) (-72197838200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1181984191769511 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (38321995852 / 1000000000000) (38321995853 / 1000000000000), orderedInterval (26123588465 / 1000000000000) (26123588466 / 1000000000000)))) (orderedInterval (-16427470229 / 1000000000000) (-16427470143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (870644205938143 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-53782644163 / 1000000000000) (-53782643837 / 1000000000000), orderedInterval (5801695611 / 1000000000000) (5801695937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1491863686530139 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (4064618107 / 1000000000000) (4064618111 / 1000000000000), orderedInterval (-41119823096 / 1000000000000) (-41119823092 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1098900039248401 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39162085275 / 1000000000000) (-39161993471 / 1000000000000), orderedInterval (28064646400 / 1000000000000) (28064738204 / 1000000000000)))) (orderedInterval (-6064956382 / 1000000000000) (-6064946186 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate315_chunkChecks4_1 :
    compactCertificate315.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1685995255034623 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37554316918 / 1000000000000) (37554316925 / 1000000000000), orderedInterval (9957641455 / 1000000000000) (9957641463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (973409814346567 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40283089624 / 1000000000000) (-40282978804 / 1000000000000), orderedInterval (31599621171 / 1000000000000) (31599731992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1727332797268403 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-30582009955 / 1000000000000) (-30581954231 / 1000000000000), orderedInterval (23251068581 / 1000000000000) (23251124305 / 1000000000000)))) (orderedInterval (-294586890402 / 1000000000000) (-294586646569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1613898362925407 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33548259358 / 1000000000000) (33548358844 / 1000000000000), orderedInterval (-21310234946 / 1000000000000) (-21310135459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1151754024665231 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14032710744 / 1000000000000) (-14032710596 / 1000000000000), orderedInterval (44902459779 / 1000000000000) (44902459926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1305966308906649 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23116525575 / 1000000000000) (23116525576 / 1000000000000), orderedInterval (37587841879 / 1000000000000) (37587841880 / 1000000000000)))) (orderedInterval (-20799669687 / 1000000000000) (-20799631547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1088778554534281 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16081578279 / 1000000000000) (16081578545 / 1000000000000), orderedInterval (-45639036810 / 1000000000000) (-45639036544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (961968872271901 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30125944056 / 1000000000000) (30125952661 / 1000000000000), orderedInterval (-41770938433 / 1000000000000) (-41770929828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (278816073722199 / 800000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23719667099 / 1000000000000) (-23719667098 / 1000000000000), orderedInterval (-35518964279 / 1000000000000) (-35518964278 / 1000000000000)))) (orderedInterval (-10882174227 / 1000000000000) (-10882172803 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate315_chunkChecks4_2 :
    compactCertificate315.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (771219933201653 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53324735836 / 1000000000000) (-53324729014 / 1000000000000), orderedInterval (21547376258 / 1000000000000) (21547383080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (653771678401933 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47489423671 / 1000000000000) (47489423672 / 1000000000000), orderedInterval (40349296743 / 1000000000000) (40349296744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (409099960751599 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45415756736 / 1000000000000) (45415771879 / 1000000000000), orderedInterval (-64735767142 / 1000000000000) (-64735751999 / 1000000000000)))) (orderedInterval (7881979291 / 1000000000000) (7881980581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (220015319497233 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74248112490 / 1000000000000) (-74248040631 / 1000000000000), orderedInterval (78529477418 / 1000000000000) (78529549277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (597384391510699 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40327846147 / 1000000000000) (-40327826186 / 1000000000000), orderedInterval (51480749649 / 1000000000000) (51480769610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (815677314645323 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26816442432 / 1000000000000) (-26816442431 / 1000000000000), orderedInterval (-48952644275 / 1000000000000) (-48952644274 / 1000000000000)))) (orderedInterval (3228769354 / 1000000000000) (3228769568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (344900039248401 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70173362993 / 1000000000000) (-70173324526 / 1000000000000), orderedInterval (49994165109 / 1000000000000) (49994203575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1401999511267121 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23122121719 / 1000000000000) (-23122118952 / 1000000000000), orderedInterval (35833651108 / 1000000000000) (35833653874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (936470699171839 / 4000000000000) 4 (IntervalRat.scale (377 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34263073242 / 1000000000000) (34263094855 / 1000000000000), orderedInterval (-39383129722 / 1000000000000) (-39383108110 / 1000000000000)))) (orderedInterval (7135337675 / 1000000000000) (7135350394 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate315_chunkChecks4 :
    compactCertificate315.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate315.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate315_chunkChecks4_0
    compactCertificate315_chunkChecks4_1 compactCertificate315_chunkChecks4_2

theorem compactCertificate315_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate315.chunkCheck r b = true :=
  compactCertificate315.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate315_chunkChecks0
    · exact compactCertificate315_chunkChecks1
    · exact compactCertificate315_chunkChecks2
    · exact compactCertificate315_chunkChecks3
    · exact compactCertificate315_chunkChecks4)

theorem compactCertificate315_coefficient0 :
    compactCertificate315.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate315_coefficient1 :
    compactCertificate315.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate315_coefficient2 :
    compactCertificate315.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate315_coefficient3 :
    compactCertificate315.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate315_coefficient4 :
    compactCertificate315.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate315_coefficients : ∀ r : Fin 5,
    compactCertificate315.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate315_coefficient0
  · exact compactCertificate315_coefficient1
  · exact compactCertificate315_coefficient2
  · exact compactCertificate315_coefficient3
  · exact compactCertificate315_coefficient4

theorem compactCertificate315_lower : (1 : ℚ) ≤ compactCertificate315.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate315, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate315_proves {t : ℝ} (ht : t ∈ compactCertificate315.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate315.proves compactCertificate315_states compactCertificate315_chunks
    compactCertificate315_coefficients compactCertificate315_lower ht

end Erdos232
