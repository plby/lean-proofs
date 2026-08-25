/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate572 : CompactCertificate where
  left := 443
  right := 444
  center := 887 / 2
  grid := fun i =>
    match i.val with
    | 0 => 141
    | 1 => 104
    | 2 => 168
    | 3 => 30
    | 4 => 82
    | 5 => 221
    | 6 => 163
    | 7 => 279
    | 8 => 206
    | 9 => 316
    | 10 => 182
    | 11 => 324
    | 12 => 302
    | 13 => 216
    | 14 => 245
    | 15 => 204
    | 16 => 180
    | 17 => 261
    | 18 => 144
    | 19 => 122
    | 20 => 77
    | 21 => 41
    | 22 => 112
    | 23 => 153
    | 24 => 65
    | 25 => 263
    | _ => 175
  point := fun i =>
    match i.val with
    | 0 => 887 / 2
    | 1 => 1306720370788187 / 4000000000000
    | 2 => 422566519648571 / 800000000000
    | 3 => 381297745189009 / 4000000000000
    | 4 => 1024219377542173 / 4000000000000
    | 5 => 2780954849070441 / 4000000000000
    | 6 => 2048438755085233 / 4000000000000
    | 7 => 3510034721358709 / 4000000000000
    | 8 => 2585475689160031 / 4000000000000
    | 9 => 3966784592084113 / 4000000000000
    | 10 => 2290224152056777 / 4000000000000
    | 11 => 4064042947419293 / 4000000000000
    | 12 => 3797156095264817 / 4000000000000
    | 13 => 2709829760949761 / 4000000000000
    | 14 => 3072658132626519 / 4000000000000
    | 15 => 2561662010270311 / 4000000000000
    | 16 => 2263306073488531 / 4000000000000
    | 17 => 655994316688569 / 800000000000
    | 18 => 1814514803050043 / 4000000000000
    | 19 => 1538184293746723 / 4000000000000
    | 20 => 962524310839969 / 4000000000000
    | 21 => 517648775581023 / 4000000000000
    | 22 => 1405517122732069 / 4000000000000
    | 23 => 1919113469735813 / 4000000000000
    | 24 => 811475689160031 / 4000000000000
    | 25 => 3298603624652351 / 4000000000000
    | _ => 2203314350571409 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36707139708 / 1000000000000) (-36707139698 / 1000000000000), orderedInterval (-9341041781 / 1000000000000) (-9341041771 / 1000000000000))
    | 1 => (orderedInterval (29749022417 / 1000000000000) (29749022418 / 1000000000000), orderedInterval (32569676151 / 1000000000000) (32569676152 / 1000000000000))
    | 2 => (orderedInterval (32428985416 / 1000000000000) (32428985419 / 1000000000000), orderedInterval (12363036509 / 1000000000000) (12363036513 / 1000000000000))
    | 3 => (orderedInterval (78310109348 / 1000000000000) (78310110824 / 1000000000000), orderedInterval (-23775309397 / 1000000000000) (-23775307921 / 1000000000000))
    | 4 => (orderedInterval (-34741158912 / 1000000000000) (-34741126777 / 1000000000000), orderedInterval (35835355608 / 1000000000000) (35835387742 / 1000000000000))
    | 5 => (orderedInterval (-29868182759 / 1000000000000) (-29868173155 / 1000000000000), orderedInterval (4877078043 / 1000000000000) (4877087647 / 1000000000000))
    | 6 => (orderedInterval (-25664006301 / 1000000000000) (-25664006300 / 1000000000000), orderedInterval (-24151179458 / 1000000000000) (-24151179457 / 1000000000000))
    | 7 => (orderedInterval (-26292752699 / 1000000000000) (-26292712943 / 1000000000000), orderedInterval (5861114818 / 1000000000000) (5861154574 / 1000000000000))
    | 8 => (orderedInterval (-438084431 / 1000000000000) (-438084430 / 1000000000000), orderedInterval (31380673916 / 1000000000000) (31380673917 / 1000000000000))
    | 9 => (orderedInterval (-6559074775 / 1000000000000) (-6559074774 / 1000000000000), orderedInterval (24476333833 / 1000000000000) (24476333834 / 1000000000000))
    | 10 => (orderedInterval (33345014136 / 1000000000000) (33345014970 / 1000000000000), orderedInterval (-47745639 / 1000000000000) (-47744806 / 1000000000000))
    | 11 => (orderedInterval (-22077030173 / 1000000000000) (-22077014396 / 1000000000000), orderedInterval (11808851332 / 1000000000000) (11808867109 / 1000000000000))
    | 12 => (orderedInterval (25042750844 / 1000000000000) (25042751206 / 1000000000000), orderedInterval (6581391530 / 1000000000000) (6581391892 / 1000000000000))
    | 13 => (orderedInterval (-10262265998 / 1000000000000) (-10262265983 / 1000000000000), orderedInterval (28893648731 / 1000000000000) (28893648745 / 1000000000000))
    | 14 => (orderedInterval (19420634158 / 1000000000000) (19420635834 / 1000000000000), orderedInterval (-21263368748 / 1000000000000) (-21263367072 / 1000000000000))
    | 15 => (orderedInterval (9792283546 / 1000000000000) (9792283547 / 1000000000000), orderedInterval (29962080253 / 1000000000000) (29962080254 / 1000000000000))
    | 16 => (orderedInterval (30264772780 / 1000000000000) (30264772781 / 1000000000000), orderedInterval (14435552702 / 1000000000000) (14435552704 / 1000000000000))
    | 17 => (orderedInterval (-20418930896 / 1000000000000) (-20418930895 / 1000000000000), orderedInterval (-18946440453 / 1000000000000) (-18946440452 / 1000000000000))
    | 18 => (orderedInterval (33672151127 / 1000000000000) (33672198648 / 1000000000000), orderedInterval (-16455968447 / 1000000000000) (-16455920926 / 1000000000000))
    | 19 => (orderedInterval (35975705669 / 1000000000000) (35975752097 / 1000000000000), orderedInterval (-19053530768 / 1000000000000) (-19053484340 / 1000000000000))
    | 20 => (orderedInterval (24056019216 / 1000000000000) (24056021169 / 1000000000000), orderedInterval (-45513563080 / 1000000000000) (-45513561127 / 1000000000000))
    | 21 => (orderedInterval (-69011084489 / 1000000000000) (-69011084486 / 1000000000000), orderedInterval (-12253520267 / 1000000000000) (-12253520264 / 1000000000000))
    | 22 => (orderedInterval (12820351780 / 1000000000000) (12820351781 / 1000000000000), orderedInterval (40570103685 / 1000000000000) (40570103686 / 1000000000000))
    | 23 => (orderedInterval (3642795656 / 1000000000000) (3642795658 / 1000000000000), orderedInterval (-36247893995 / 1000000000000) (-36247893993 / 1000000000000))
    | 24 => (orderedInterval (29271479655 / 1000000000000) (29271484447 / 1000000000000), orderedInterval (-47834776718 / 1000000000000) (-47834771926 / 1000000000000))
    | 25 => (orderedInterval (19983973223 / 1000000000000) (19983975671 / 1000000000000), orderedInterval (-19315686184 / 1000000000000) (-19315683735 / 1000000000000))
    | _ => (orderedInterval (-32816271718 / 1000000000000) (-32816258810 / 1000000000000), orderedInterval (8909063187 / 1000000000000) (8909076095 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12369252180 / 1000000000000) (-12369252145 / 1000000000000)
      | 1 => orderedInterval (5248130 / 1000000000000) (5250055 / 1000000000000)
      | 2 => orderedInterval (800384815 / 1000000000000) (800386067 / 1000000000000)
      | 3 => orderedInterval (497679540 / 1000000000000) (497682020 / 1000000000000)
      | 4 => orderedInterval (-1520807856 / 1000000000000) (-1520807786 / 1000000000000)
      | 5 => orderedInterval (-2141679625 / 1000000000000) (-2141679582 / 1000000000000)
      | 6 => orderedInterval (-6637005886 / 1000000000000) (-6636995485 / 1000000000000)
      | 7 => orderedInterval (704264428 / 1000000000000) (704264482 / 1000000000000)
      | _ => orderedInterval (4706927557 / 1000000000000) (4706930330 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2614872794 / 1000000000000) (-2614872755 / 1000000000000)
      | 1 => orderedInterval (267343967 / 1000000000000) (267345779 / 1000000000000)
      | 2 => orderedInterval (747631756 / 1000000000000) (747634225 / 1000000000000)
      | 3 => orderedInterval (-5883844090 / 1000000000000) (-5883838508 / 1000000000000)
      | 4 => orderedInterval (4105666489 / 1000000000000) (4105666605 / 1000000000000)
      | 5 => orderedInterval (-1451254549 / 1000000000000) (-1451254487 / 1000000000000)
      | 6 => orderedInterval (2822407169 / 1000000000000) (2822417357 / 1000000000000)
      | 7 => orderedInterval (2342033570 / 1000000000000) (2342033619 / 1000000000000)
      | _ => orderedInterval (715604482 / 1000000000000) (715608047 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11705595243 / 1000000000000) (11705595287 / 1000000000000)
      | 1 => orderedInterval (-4756433218 / 1000000000000) (-4756431061 / 1000000000000)
      | 2 => orderedInterval (-3154040437 / 1000000000000) (-3154035553 / 1000000000000)
      | 3 => orderedInterval (6539067084 / 1000000000000) (6539079751 / 1000000000000)
      | 4 => orderedInterval (4621216996 / 1000000000000) (4621217197 / 1000000000000)
      | 5 => orderedInterval (4373818174 / 1000000000000) (4373818266 / 1000000000000)
      | 6 => orderedInterval (6926593911 / 1000000000000) (6926603976 / 1000000000000)
      | 7 => orderedInterval (395514003 / 1000000000000) (395514051 / 1000000000000)
      | _ => orderedInterval (-3912166651 / 1000000000000) (-3912161958 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (2329138240 / 1000000000000) (2329138291 / 1000000000000)
      | 1 => orderedInterval (1091993191 / 1000000000000) (1091996178 / 1000000000000)
      | 2 => orderedInterval (-940389776 / 1000000000000) (-940380127 / 1000000000000)
      | 3 => orderedInterval (28434735387 / 1000000000000) (28434764224 / 1000000000000)
      | 4 => orderedInterval (-9142788703 / 1000000000000) (-9142788349 / 1000000000000)
      | 5 => orderedInterval (3729986712 / 1000000000000) (3729986853 / 1000000000000)
      | 6 => orderedInterval (-3297545565 / 1000000000000) (-3297535593 / 1000000000000)
      | 7 => orderedInterval (-3065756736 / 1000000000000) (-3065756687 / 1000000000000)
      | _ => orderedInterval (-6869227886 / 1000000000000) (-6869221559 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10649331283 / 1000000000000) (-10649331224 / 1000000000000)
      | 1 => orderedInterval (12674903162 / 1000000000000) (12674907621 / 1000000000000)
      | 2 => orderedInterval (12385487250 / 1000000000000) (12385506345 / 1000000000000)
      | 3 => orderedInterval (-50570615571 / 1000000000000) (-50570549699 / 1000000000000)
      | 4 => orderedInterval (-15616418951 / 1000000000000) (-15616418312 / 1000000000000)
      | 5 => orderedInterval (-10223408885 / 1000000000000) (-10223408661 / 1000000000000)
      | 6 => orderedInterval (-6961016101 / 1000000000000) (-6961006156 / 1000000000000)
      | 7 => orderedInterval (-473899238 / 1000000000000) (-473899186 / 1000000000000)
      | _ => orderedInterval (-4755688872 / 1000000000000) (-4755680069 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-15954241077 / 1000000000000) (-15954222044 / 1000000000000)
    | 1 => orderedInterval (1050716000 / 1000000000000) (1050739882 / 1000000000000)
    | 2 => orderedInterval (22739165105 / 1000000000000) (22739199956 / 1000000000000)
    | 3 => orderedInterval (12270144864 / 1000000000000) (12270203231 / 1000000000000)
    | _ => orderedInterval (-74189988489 / 1000000000000) (-74189879341 / 1000000000000)

theorem compactCertificate572_stateChecks0 :
    compactCertificate572.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (887 / 2)) (orderedInterval (-36707139708 / 1000000000000) (-36707139698 / 1000000000000), orderedInterval (-9341041781 / 1000000000000) (-9341041771 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1306720370788187 / 4000000000000)) (orderedInterval (29749022417 / 1000000000000) (29749022418 / 1000000000000), orderedInterval (32569676151 / 1000000000000) (32569676152 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (422566519648571 / 800000000000)) (orderedInterval (32428985416 / 1000000000000) (32428985419 / 1000000000000), orderedInterval (12363036509 / 1000000000000) (12363036513 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks1 :
    compactCertificate572.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (381297745189009 / 4000000000000)) (orderedInterval (78310109348 / 1000000000000) (78310110824 / 1000000000000), orderedInterval (-23775309397 / 1000000000000) (-23775307921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1024219377542173 / 4000000000000)) (orderedInterval (-34741158912 / 1000000000000) (-34741126777 / 1000000000000), orderedInterval (35835355608 / 1000000000000) (35835387742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2780954849070441 / 4000000000000)) (orderedInterval (-29868182759 / 1000000000000) (-29868173155 / 1000000000000), orderedInterval (4877078043 / 1000000000000) (4877087647 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks2 :
    compactCertificate572.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2048438755085233 / 4000000000000)) (orderedInterval (-25664006301 / 1000000000000) (-25664006300 / 1000000000000), orderedInterval (-24151179458 / 1000000000000) (-24151179457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (3510034721358709 / 4000000000000)) (orderedInterval (-26292752699 / 1000000000000) (-26292712943 / 1000000000000), orderedInterval (5861114818 / 1000000000000) (5861154574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2585475689160031 / 4000000000000)) (orderedInterval (-438084431 / 1000000000000) (-438084430 / 1000000000000), orderedInterval (31380673916 / 1000000000000) (31380673917 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks3 :
    compactCertificate572.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 316 12 (3966784592084113 / 4000000000000)) (orderedInterval (-6559074775 / 1000000000000) (-6559074774 / 1000000000000), orderedInterval (24476333833 / 1000000000000) (24476333834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2290224152056777 / 4000000000000)) (orderedInterval (33345014136 / 1000000000000) (33345014970 / 1000000000000), orderedInterval (-47745639 / 1000000000000) (-47744806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 324 12 (4064042947419293 / 4000000000000)) (orderedInterval (-22077030173 / 1000000000000) (-22077014396 / 1000000000000), orderedInterval (11808851332 / 1000000000000) (11808867109 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks4 :
    compactCertificate572.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (3797156095264817 / 4000000000000)) (orderedInterval (25042750844 / 1000000000000) (25042751206 / 1000000000000), orderedInterval (6581391530 / 1000000000000) (6581391892 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2709829760949761 / 4000000000000)) (orderedInterval (-10262265998 / 1000000000000) (-10262265983 / 1000000000000), orderedInterval (28893648731 / 1000000000000) (28893648745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3072658132626519 / 4000000000000)) (orderedInterval (19420634158 / 1000000000000) (19420635834 / 1000000000000), orderedInterval (-21263368748 / 1000000000000) (-21263367072 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks5 :
    compactCertificate572.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2561662010270311 / 4000000000000)) (orderedInterval (9792283546 / 1000000000000) (9792283547 / 1000000000000), orderedInterval (29962080253 / 1000000000000) (29962080254 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2263306073488531 / 4000000000000)) (orderedInterval (30264772780 / 1000000000000) (30264772781 / 1000000000000), orderedInterval (14435552702 / 1000000000000) (14435552704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (655994316688569 / 800000000000)) (orderedInterval (-20418930896 / 1000000000000) (-20418930895 / 1000000000000), orderedInterval (-18946440453 / 1000000000000) (-18946440452 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks6 :
    compactCertificate572.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1814514803050043 / 4000000000000)) (orderedInterval (33672151127 / 1000000000000) (33672198648 / 1000000000000), orderedInterval (-16455968447 / 1000000000000) (-16455920926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1538184293746723 / 4000000000000)) (orderedInterval (35975705669 / 1000000000000) (35975752097 / 1000000000000), orderedInterval (-19053530768 / 1000000000000) (-19053484340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (962524310839969 / 4000000000000)) (orderedInterval (24056019216 / 1000000000000) (24056021169 / 1000000000000), orderedInterval (-45513563080 / 1000000000000) (-45513561127 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks7 :
    compactCertificate572.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (517648775581023 / 4000000000000)) (orderedInterval (-69011084489 / 1000000000000) (-69011084486 / 1000000000000), orderedInterval (-12253520267 / 1000000000000) (-12253520264 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1405517122732069 / 4000000000000)) (orderedInterval (12820351780 / 1000000000000) (12820351781 / 1000000000000), orderedInterval (40570103685 / 1000000000000) (40570103686 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1919113469735813 / 4000000000000)) (orderedInterval (3642795656 / 1000000000000) (3642795658 / 1000000000000), orderedInterval (-36247893995 / 1000000000000) (-36247893993 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_stateChecks8 :
    compactCertificate572.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (811475689160031 / 4000000000000)) (orderedInterval (29271479655 / 1000000000000) (29271484447 / 1000000000000), orderedInterval (-47834776718 / 1000000000000) (-47834771926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (3298603624652351 / 4000000000000)) (orderedInterval (19983973223 / 1000000000000) (19983975671 / 1000000000000), orderedInterval (-19315686184 / 1000000000000) (-19315683735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2203314350571409 / 4000000000000)) (orderedInterval (-32816271718 / 1000000000000) (-32816258810 / 1000000000000), orderedInterval (8909063187 / 1000000000000) (8909076095 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_states : ∀ j,
    BesselStateValid (compactCertificate572.point j) (compactCertificate572.state j) :=
  compactCertificate572.statesValid_of_checks3 compactCertificate572_stateChecks0
    compactCertificate572_stateChecks1 compactCertificate572_stateChecks2
    compactCertificate572_stateChecks3 compactCertificate572_stateChecks4
    compactCertificate572_stateChecks5 compactCertificate572_stateChecks6
    compactCertificate572_stateChecks7 compactCertificate572_stateChecks8

theorem compactCertificate572_chunkChecks0_0 :
    compactCertificate572.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (887 / 2) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36707139708 / 1000000000000) (-36707139698 / 1000000000000), orderedInterval (-9341041781 / 1000000000000) (-9341041771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1306720370788187 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29749022417 / 1000000000000) (29749022418 / 1000000000000), orderedInterval (32569676151 / 1000000000000) (32569676152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (422566519648571 / 800000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32428985416 / 1000000000000) (32428985419 / 1000000000000), orderedInterval (12363036509 / 1000000000000) (12363036513 / 1000000000000)))) (orderedInterval (-12369252180 / 1000000000000) (-12369252145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (381297745189009 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78310109348 / 1000000000000) (78310110824 / 1000000000000), orderedInterval (-23775309397 / 1000000000000) (-23775307921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1024219377542173 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34741158912 / 1000000000000) (-34741126777 / 1000000000000), orderedInterval (35835355608 / 1000000000000) (35835387742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2780954849070441 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29868182759 / 1000000000000) (-29868173155 / 1000000000000), orderedInterval (4877078043 / 1000000000000) (4877087647 / 1000000000000)))) (orderedInterval (5248130 / 1000000000000) (5250055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2048438755085233 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664006301 / 1000000000000) (-25664006300 / 1000000000000), orderedInterval (-24151179458 / 1000000000000) (-24151179457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3510034721358709 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26292752699 / 1000000000000) (-26292712943 / 1000000000000), orderedInterval (5861114818 / 1000000000000) (5861154574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2585475689160031 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-438084431 / 1000000000000) (-438084430 / 1000000000000), orderedInterval (31380673916 / 1000000000000) (31380673917 / 1000000000000)))) (orderedInterval (800384815 / 1000000000000) (800386067 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks0_1 :
    compactCertificate572.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3966784592084113 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6559074775 / 1000000000000) (-6559074774 / 1000000000000), orderedInterval (24476333833 / 1000000000000) (24476333834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2290224152056777 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33345014136 / 1000000000000) (33345014970 / 1000000000000), orderedInterval (-47745639 / 1000000000000) (-47744806 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4064042947419293 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22077030173 / 1000000000000) (-22077014396 / 1000000000000), orderedInterval (11808851332 / 1000000000000) (11808867109 / 1000000000000)))) (orderedInterval (497679540 / 1000000000000) (497682020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3797156095264817 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25042750844 / 1000000000000) (25042751206 / 1000000000000), orderedInterval (6581391530 / 1000000000000) (6581391892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2709829760949761 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10262265998 / 1000000000000) (-10262265983 / 1000000000000), orderedInterval (28893648731 / 1000000000000) (28893648745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3072658132626519 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19420634158 / 1000000000000) (19420635834 / 1000000000000), orderedInterval (-21263368748 / 1000000000000) (-21263367072 / 1000000000000)))) (orderedInterval (-1520807856 / 1000000000000) (-1520807786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2561662010270311 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9792283546 / 1000000000000) (9792283547 / 1000000000000), orderedInterval (29962080253 / 1000000000000) (29962080254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2263306073488531 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30264772780 / 1000000000000) (30264772781 / 1000000000000), orderedInterval (14435552702 / 1000000000000) (14435552704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (655994316688569 / 800000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20418930896 / 1000000000000) (-20418930895 / 1000000000000), orderedInterval (-18946440453 / 1000000000000) (-18946440452 / 1000000000000)))) (orderedInterval (-2141679625 / 1000000000000) (-2141679582 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks0_2 :
    compactCertificate572.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1814514803050043 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33672151127 / 1000000000000) (33672198648 / 1000000000000), orderedInterval (-16455968447 / 1000000000000) (-16455920926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1538184293746723 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35975705669 / 1000000000000) (35975752097 / 1000000000000), orderedInterval (-19053530768 / 1000000000000) (-19053484340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (962524310839969 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24056019216 / 1000000000000) (24056021169 / 1000000000000), orderedInterval (-45513563080 / 1000000000000) (-45513561127 / 1000000000000)))) (orderedInterval (-6637005886 / 1000000000000) (-6636995485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (517648775581023 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69011084489 / 1000000000000) (-69011084486 / 1000000000000), orderedInterval (-12253520267 / 1000000000000) (-12253520264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1405517122732069 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12820351780 / 1000000000000) (12820351781 / 1000000000000), orderedInterval (40570103685 / 1000000000000) (40570103686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1919113469735813 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3642795656 / 1000000000000) (3642795658 / 1000000000000), orderedInterval (-36247893995 / 1000000000000) (-36247893993 / 1000000000000)))) (orderedInterval (704264428 / 1000000000000) (704264482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (811475689160031 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29271479655 / 1000000000000) (29271484447 / 1000000000000), orderedInterval (-47834776718 / 1000000000000) (-47834771926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3298603624652351 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19983973223 / 1000000000000) (19983975671 / 1000000000000), orderedInterval (-19315686184 / 1000000000000) (-19315683735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2203314350571409 / 4000000000000) 0 (IntervalRat.scale (887 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32816271718 / 1000000000000) (-32816258810 / 1000000000000), orderedInterval (8909063187 / 1000000000000) (8909076095 / 1000000000000)))) (orderedInterval (4706927557 / 1000000000000) (4706930330 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks0 :
    compactCertificate572.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate572.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate572_chunkChecks0_0
    compactCertificate572_chunkChecks0_1 compactCertificate572_chunkChecks0_2

theorem compactCertificate572_chunkChecks1_0 :
    compactCertificate572.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (887 / 2) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36707139708 / 1000000000000) (-36707139698 / 1000000000000), orderedInterval (-9341041781 / 1000000000000) (-9341041771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1306720370788187 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29749022417 / 1000000000000) (29749022418 / 1000000000000), orderedInterval (32569676151 / 1000000000000) (32569676152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (422566519648571 / 800000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32428985416 / 1000000000000) (32428985419 / 1000000000000), orderedInterval (12363036509 / 1000000000000) (12363036513 / 1000000000000)))) (orderedInterval (-2614872794 / 1000000000000) (-2614872755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (381297745189009 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78310109348 / 1000000000000) (78310110824 / 1000000000000), orderedInterval (-23775309397 / 1000000000000) (-23775307921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1024219377542173 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34741158912 / 1000000000000) (-34741126777 / 1000000000000), orderedInterval (35835355608 / 1000000000000) (35835387742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2780954849070441 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29868182759 / 1000000000000) (-29868173155 / 1000000000000), orderedInterval (4877078043 / 1000000000000) (4877087647 / 1000000000000)))) (orderedInterval (267343967 / 1000000000000) (267345779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2048438755085233 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664006301 / 1000000000000) (-25664006300 / 1000000000000), orderedInterval (-24151179458 / 1000000000000) (-24151179457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3510034721358709 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26292752699 / 1000000000000) (-26292712943 / 1000000000000), orderedInterval (5861114818 / 1000000000000) (5861154574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2585475689160031 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-438084431 / 1000000000000) (-438084430 / 1000000000000), orderedInterval (31380673916 / 1000000000000) (31380673917 / 1000000000000)))) (orderedInterval (747631756 / 1000000000000) (747634225 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks1_1 :
    compactCertificate572.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3966784592084113 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6559074775 / 1000000000000) (-6559074774 / 1000000000000), orderedInterval (24476333833 / 1000000000000) (24476333834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2290224152056777 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33345014136 / 1000000000000) (33345014970 / 1000000000000), orderedInterval (-47745639 / 1000000000000) (-47744806 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4064042947419293 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22077030173 / 1000000000000) (-22077014396 / 1000000000000), orderedInterval (11808851332 / 1000000000000) (11808867109 / 1000000000000)))) (orderedInterval (-5883844090 / 1000000000000) (-5883838508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3797156095264817 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25042750844 / 1000000000000) (25042751206 / 1000000000000), orderedInterval (6581391530 / 1000000000000) (6581391892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2709829760949761 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10262265998 / 1000000000000) (-10262265983 / 1000000000000), orderedInterval (28893648731 / 1000000000000) (28893648745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3072658132626519 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19420634158 / 1000000000000) (19420635834 / 1000000000000), orderedInterval (-21263368748 / 1000000000000) (-21263367072 / 1000000000000)))) (orderedInterval (4105666489 / 1000000000000) (4105666605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2561662010270311 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9792283546 / 1000000000000) (9792283547 / 1000000000000), orderedInterval (29962080253 / 1000000000000) (29962080254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2263306073488531 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30264772780 / 1000000000000) (30264772781 / 1000000000000), orderedInterval (14435552702 / 1000000000000) (14435552704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (655994316688569 / 800000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20418930896 / 1000000000000) (-20418930895 / 1000000000000), orderedInterval (-18946440453 / 1000000000000) (-18946440452 / 1000000000000)))) (orderedInterval (-1451254549 / 1000000000000) (-1451254487 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks1_2 :
    compactCertificate572.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1814514803050043 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33672151127 / 1000000000000) (33672198648 / 1000000000000), orderedInterval (-16455968447 / 1000000000000) (-16455920926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1538184293746723 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35975705669 / 1000000000000) (35975752097 / 1000000000000), orderedInterval (-19053530768 / 1000000000000) (-19053484340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (962524310839969 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24056019216 / 1000000000000) (24056021169 / 1000000000000), orderedInterval (-45513563080 / 1000000000000) (-45513561127 / 1000000000000)))) (orderedInterval (2822407169 / 1000000000000) (2822417357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (517648775581023 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69011084489 / 1000000000000) (-69011084486 / 1000000000000), orderedInterval (-12253520267 / 1000000000000) (-12253520264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1405517122732069 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12820351780 / 1000000000000) (12820351781 / 1000000000000), orderedInterval (40570103685 / 1000000000000) (40570103686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1919113469735813 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3642795656 / 1000000000000) (3642795658 / 1000000000000), orderedInterval (-36247893995 / 1000000000000) (-36247893993 / 1000000000000)))) (orderedInterval (2342033570 / 1000000000000) (2342033619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (811475689160031 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29271479655 / 1000000000000) (29271484447 / 1000000000000), orderedInterval (-47834776718 / 1000000000000) (-47834771926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3298603624652351 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19983973223 / 1000000000000) (19983975671 / 1000000000000), orderedInterval (-19315686184 / 1000000000000) (-19315683735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2203314350571409 / 4000000000000) 1 (IntervalRat.scale (887 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32816271718 / 1000000000000) (-32816258810 / 1000000000000), orderedInterval (8909063187 / 1000000000000) (8909076095 / 1000000000000)))) (orderedInterval (715604482 / 1000000000000) (715608047 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks1 :
    compactCertificate572.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate572.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate572_chunkChecks1_0
    compactCertificate572_chunkChecks1_1 compactCertificate572_chunkChecks1_2

theorem compactCertificate572_chunkChecks2_0 :
    compactCertificate572.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (887 / 2) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36707139708 / 1000000000000) (-36707139698 / 1000000000000), orderedInterval (-9341041781 / 1000000000000) (-9341041771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1306720370788187 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29749022417 / 1000000000000) (29749022418 / 1000000000000), orderedInterval (32569676151 / 1000000000000) (32569676152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (422566519648571 / 800000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32428985416 / 1000000000000) (32428985419 / 1000000000000), orderedInterval (12363036509 / 1000000000000) (12363036513 / 1000000000000)))) (orderedInterval (11705595243 / 1000000000000) (11705595287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (381297745189009 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78310109348 / 1000000000000) (78310110824 / 1000000000000), orderedInterval (-23775309397 / 1000000000000) (-23775307921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1024219377542173 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34741158912 / 1000000000000) (-34741126777 / 1000000000000), orderedInterval (35835355608 / 1000000000000) (35835387742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2780954849070441 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29868182759 / 1000000000000) (-29868173155 / 1000000000000), orderedInterval (4877078043 / 1000000000000) (4877087647 / 1000000000000)))) (orderedInterval (-4756433218 / 1000000000000) (-4756431061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2048438755085233 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664006301 / 1000000000000) (-25664006300 / 1000000000000), orderedInterval (-24151179458 / 1000000000000) (-24151179457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3510034721358709 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26292752699 / 1000000000000) (-26292712943 / 1000000000000), orderedInterval (5861114818 / 1000000000000) (5861154574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2585475689160031 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-438084431 / 1000000000000) (-438084430 / 1000000000000), orderedInterval (31380673916 / 1000000000000) (31380673917 / 1000000000000)))) (orderedInterval (-3154040437 / 1000000000000) (-3154035553 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks2_1 :
    compactCertificate572.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3966784592084113 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6559074775 / 1000000000000) (-6559074774 / 1000000000000), orderedInterval (24476333833 / 1000000000000) (24476333834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2290224152056777 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33345014136 / 1000000000000) (33345014970 / 1000000000000), orderedInterval (-47745639 / 1000000000000) (-47744806 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4064042947419293 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22077030173 / 1000000000000) (-22077014396 / 1000000000000), orderedInterval (11808851332 / 1000000000000) (11808867109 / 1000000000000)))) (orderedInterval (6539067084 / 1000000000000) (6539079751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3797156095264817 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25042750844 / 1000000000000) (25042751206 / 1000000000000), orderedInterval (6581391530 / 1000000000000) (6581391892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2709829760949761 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10262265998 / 1000000000000) (-10262265983 / 1000000000000), orderedInterval (28893648731 / 1000000000000) (28893648745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3072658132626519 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19420634158 / 1000000000000) (19420635834 / 1000000000000), orderedInterval (-21263368748 / 1000000000000) (-21263367072 / 1000000000000)))) (orderedInterval (4621216996 / 1000000000000) (4621217197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2561662010270311 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9792283546 / 1000000000000) (9792283547 / 1000000000000), orderedInterval (29962080253 / 1000000000000) (29962080254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2263306073488531 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30264772780 / 1000000000000) (30264772781 / 1000000000000), orderedInterval (14435552702 / 1000000000000) (14435552704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (655994316688569 / 800000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20418930896 / 1000000000000) (-20418930895 / 1000000000000), orderedInterval (-18946440453 / 1000000000000) (-18946440452 / 1000000000000)))) (orderedInterval (4373818174 / 1000000000000) (4373818266 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks2_2 :
    compactCertificate572.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1814514803050043 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33672151127 / 1000000000000) (33672198648 / 1000000000000), orderedInterval (-16455968447 / 1000000000000) (-16455920926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1538184293746723 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35975705669 / 1000000000000) (35975752097 / 1000000000000), orderedInterval (-19053530768 / 1000000000000) (-19053484340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (962524310839969 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24056019216 / 1000000000000) (24056021169 / 1000000000000), orderedInterval (-45513563080 / 1000000000000) (-45513561127 / 1000000000000)))) (orderedInterval (6926593911 / 1000000000000) (6926603976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (517648775581023 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69011084489 / 1000000000000) (-69011084486 / 1000000000000), orderedInterval (-12253520267 / 1000000000000) (-12253520264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1405517122732069 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12820351780 / 1000000000000) (12820351781 / 1000000000000), orderedInterval (40570103685 / 1000000000000) (40570103686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1919113469735813 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3642795656 / 1000000000000) (3642795658 / 1000000000000), orderedInterval (-36247893995 / 1000000000000) (-36247893993 / 1000000000000)))) (orderedInterval (395514003 / 1000000000000) (395514051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (811475689160031 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29271479655 / 1000000000000) (29271484447 / 1000000000000), orderedInterval (-47834776718 / 1000000000000) (-47834771926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3298603624652351 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19983973223 / 1000000000000) (19983975671 / 1000000000000), orderedInterval (-19315686184 / 1000000000000) (-19315683735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2203314350571409 / 4000000000000) 2 (IntervalRat.scale (887 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32816271718 / 1000000000000) (-32816258810 / 1000000000000), orderedInterval (8909063187 / 1000000000000) (8909076095 / 1000000000000)))) (orderedInterval (-3912166651 / 1000000000000) (-3912161958 / 1000000000000))) = true
  rfl'

theorem compactCertificate572_chunkChecks2 :
    compactCertificate572.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate572.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate572_chunkChecks2_0
    compactCertificate572_chunkChecks2_1 compactCertificate572_chunkChecks2_2

theorem compactCertificate572_chunkChecks3_0 :
    compactCertificate572.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (887 / 2) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36707139708 / 1000000000000) (-36707139698 / 1000000000000), orderedInterval (-9341041781 / 1000000000000) (-9341041771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1306720370788187 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29749022417 / 1000000000000) (29749022418 / 1000000000000), orderedInterval (32569676151 / 1000000000000) (32569676152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (422566519648571 / 800000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32428985416 / 1000000000000) (32428985419 / 1000000000000), orderedInterval (12363036509 / 1000000000000) (12363036513 / 1000000000000)))) (orderedInterval (2329138240 / 1000000000000) (2329138291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (381297745189009 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78310109348 / 1000000000000) (78310110824 / 1000000000000), orderedInterval (-23775309397 / 1000000000000) (-23775307921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1024219377542173 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34741158912 / 1000000000000) (-34741126777 / 1000000000000), orderedInterval (35835355608 / 1000000000000) (35835387742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2780954849070441 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29868182759 / 1000000000000) (-29868173155 / 1000000000000), orderedInterval (4877078043 / 1000000000000) (4877087647 / 1000000000000)))) (orderedInterval (1091993191 / 1000000000000) (1091996178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2048438755085233 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664006301 / 1000000000000) (-25664006300 / 1000000000000), orderedInterval (-24151179458 / 1000000000000) (-24151179457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3510034721358709 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26292752699 / 1000000000000) (-26292712943 / 1000000000000), orderedInterval (5861114818 / 1000000000000) (5861154574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2585475689160031 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-438084431 / 1000000000000) (-438084430 / 1000000000000), orderedInterval (31380673916 / 1000000000000) (31380673917 / 1000000000000)))) (orderedInterval (-940389776 / 1000000000000) (-940380127 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate572_chunkChecks3_1 :
    compactCertificate572.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3966784592084113 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6559074775 / 1000000000000) (-6559074774 / 1000000000000), orderedInterval (24476333833 / 1000000000000) (24476333834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2290224152056777 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33345014136 / 1000000000000) (33345014970 / 1000000000000), orderedInterval (-47745639 / 1000000000000) (-47744806 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4064042947419293 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22077030173 / 1000000000000) (-22077014396 / 1000000000000), orderedInterval (11808851332 / 1000000000000) (11808867109 / 1000000000000)))) (orderedInterval (28434735387 / 1000000000000) (28434764224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3797156095264817 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25042750844 / 1000000000000) (25042751206 / 1000000000000), orderedInterval (6581391530 / 1000000000000) (6581391892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2709829760949761 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10262265998 / 1000000000000) (-10262265983 / 1000000000000), orderedInterval (28893648731 / 1000000000000) (28893648745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3072658132626519 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19420634158 / 1000000000000) (19420635834 / 1000000000000), orderedInterval (-21263368748 / 1000000000000) (-21263367072 / 1000000000000)))) (orderedInterval (-9142788703 / 1000000000000) (-9142788349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2561662010270311 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9792283546 / 1000000000000) (9792283547 / 1000000000000), orderedInterval (29962080253 / 1000000000000) (29962080254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2263306073488531 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30264772780 / 1000000000000) (30264772781 / 1000000000000), orderedInterval (14435552702 / 1000000000000) (14435552704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (655994316688569 / 800000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20418930896 / 1000000000000) (-20418930895 / 1000000000000), orderedInterval (-18946440453 / 1000000000000) (-18946440452 / 1000000000000)))) (orderedInterval (3729986712 / 1000000000000) (3729986853 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate572_chunkChecks3_2 :
    compactCertificate572.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1814514803050043 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33672151127 / 1000000000000) (33672198648 / 1000000000000), orderedInterval (-16455968447 / 1000000000000) (-16455920926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1538184293746723 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35975705669 / 1000000000000) (35975752097 / 1000000000000), orderedInterval (-19053530768 / 1000000000000) (-19053484340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (962524310839969 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24056019216 / 1000000000000) (24056021169 / 1000000000000), orderedInterval (-45513563080 / 1000000000000) (-45513561127 / 1000000000000)))) (orderedInterval (-3297545565 / 1000000000000) (-3297535593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (517648775581023 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69011084489 / 1000000000000) (-69011084486 / 1000000000000), orderedInterval (-12253520267 / 1000000000000) (-12253520264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1405517122732069 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12820351780 / 1000000000000) (12820351781 / 1000000000000), orderedInterval (40570103685 / 1000000000000) (40570103686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1919113469735813 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3642795656 / 1000000000000) (3642795658 / 1000000000000), orderedInterval (-36247893995 / 1000000000000) (-36247893993 / 1000000000000)))) (orderedInterval (-3065756736 / 1000000000000) (-3065756687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (811475689160031 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29271479655 / 1000000000000) (29271484447 / 1000000000000), orderedInterval (-47834776718 / 1000000000000) (-47834771926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3298603624652351 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19983973223 / 1000000000000) (19983975671 / 1000000000000), orderedInterval (-19315686184 / 1000000000000) (-19315683735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2203314350571409 / 4000000000000) 3 (IntervalRat.scale (887 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32816271718 / 1000000000000) (-32816258810 / 1000000000000), orderedInterval (8909063187 / 1000000000000) (8909076095 / 1000000000000)))) (orderedInterval (-6869227886 / 1000000000000) (-6869221559 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate572_chunkChecks3 :
    compactCertificate572.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate572.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate572_chunkChecks3_0
    compactCertificate572_chunkChecks3_1 compactCertificate572_chunkChecks3_2

theorem compactCertificate572_chunkChecks4_0 :
    compactCertificate572.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (887 / 2) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36707139708 / 1000000000000) (-36707139698 / 1000000000000), orderedInterval (-9341041781 / 1000000000000) (-9341041771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1306720370788187 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (29749022417 / 1000000000000) (29749022418 / 1000000000000), orderedInterval (32569676151 / 1000000000000) (32569676152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (422566519648571 / 800000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32428985416 / 1000000000000) (32428985419 / 1000000000000), orderedInterval (12363036509 / 1000000000000) (12363036513 / 1000000000000)))) (orderedInterval (-10649331283 / 1000000000000) (-10649331224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (381297745189009 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78310109348 / 1000000000000) (78310110824 / 1000000000000), orderedInterval (-23775309397 / 1000000000000) (-23775307921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1024219377542173 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-34741158912 / 1000000000000) (-34741126777 / 1000000000000), orderedInterval (35835355608 / 1000000000000) (35835387742 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2780954849070441 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29868182759 / 1000000000000) (-29868173155 / 1000000000000), orderedInterval (4877078043 / 1000000000000) (4877087647 / 1000000000000)))) (orderedInterval (12674903162 / 1000000000000) (12674907621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2048438755085233 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664006301 / 1000000000000) (-25664006300 / 1000000000000), orderedInterval (-24151179458 / 1000000000000) (-24151179457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3510034721358709 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26292752699 / 1000000000000) (-26292712943 / 1000000000000), orderedInterval (5861114818 / 1000000000000) (5861154574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2585475689160031 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-438084431 / 1000000000000) (-438084430 / 1000000000000), orderedInterval (31380673916 / 1000000000000) (31380673917 / 1000000000000)))) (orderedInterval (12385487250 / 1000000000000) (12385506345 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate572_chunkChecks4_1 :
    compactCertificate572.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3966784592084113 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6559074775 / 1000000000000) (-6559074774 / 1000000000000), orderedInterval (24476333833 / 1000000000000) (24476333834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2290224152056777 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33345014136 / 1000000000000) (33345014970 / 1000000000000), orderedInterval (-47745639 / 1000000000000) (-47744806 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4064042947419293 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22077030173 / 1000000000000) (-22077014396 / 1000000000000), orderedInterval (11808851332 / 1000000000000) (11808867109 / 1000000000000)))) (orderedInterval (-50570615571 / 1000000000000) (-50570549699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3797156095264817 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25042750844 / 1000000000000) (25042751206 / 1000000000000), orderedInterval (6581391530 / 1000000000000) (6581391892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2709829760949761 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10262265998 / 1000000000000) (-10262265983 / 1000000000000), orderedInterval (28893648731 / 1000000000000) (28893648745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3072658132626519 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19420634158 / 1000000000000) (19420635834 / 1000000000000), orderedInterval (-21263368748 / 1000000000000) (-21263367072 / 1000000000000)))) (orderedInterval (-15616418951 / 1000000000000) (-15616418312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2561662010270311 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9792283546 / 1000000000000) (9792283547 / 1000000000000), orderedInterval (29962080253 / 1000000000000) (29962080254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2263306073488531 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30264772780 / 1000000000000) (30264772781 / 1000000000000), orderedInterval (14435552702 / 1000000000000) (14435552704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (655994316688569 / 800000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20418930896 / 1000000000000) (-20418930895 / 1000000000000), orderedInterval (-18946440453 / 1000000000000) (-18946440452 / 1000000000000)))) (orderedInterval (-10223408885 / 1000000000000) (-10223408661 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate572_chunkChecks4_2 :
    compactCertificate572.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1814514803050043 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33672151127 / 1000000000000) (33672198648 / 1000000000000), orderedInterval (-16455968447 / 1000000000000) (-16455920926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1538184293746723 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35975705669 / 1000000000000) (35975752097 / 1000000000000), orderedInterval (-19053530768 / 1000000000000) (-19053484340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (962524310839969 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (24056019216 / 1000000000000) (24056021169 / 1000000000000), orderedInterval (-45513563080 / 1000000000000) (-45513561127 / 1000000000000)))) (orderedInterval (-6961016101 / 1000000000000) (-6961006156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (517648775581023 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69011084489 / 1000000000000) (-69011084486 / 1000000000000), orderedInterval (-12253520267 / 1000000000000) (-12253520264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1405517122732069 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12820351780 / 1000000000000) (12820351781 / 1000000000000), orderedInterval (40570103685 / 1000000000000) (40570103686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1919113469735813 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (3642795656 / 1000000000000) (3642795658 / 1000000000000), orderedInterval (-36247893995 / 1000000000000) (-36247893993 / 1000000000000)))) (orderedInterval (-473899238 / 1000000000000) (-473899186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (811475689160031 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29271479655 / 1000000000000) (29271484447 / 1000000000000), orderedInterval (-47834776718 / 1000000000000) (-47834771926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3298603624652351 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (19983973223 / 1000000000000) (19983975671 / 1000000000000), orderedInterval (-19315686184 / 1000000000000) (-19315683735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2203314350571409 / 4000000000000) 4 (IntervalRat.scale (887 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32816271718 / 1000000000000) (-32816258810 / 1000000000000), orderedInterval (8909063187 / 1000000000000) (8909076095 / 1000000000000)))) (orderedInterval (-4755688872 / 1000000000000) (-4755680069 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate572_chunkChecks4 :
    compactCertificate572.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate572.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate572_chunkChecks4_0
    compactCertificate572_chunkChecks4_1 compactCertificate572_chunkChecks4_2

theorem compactCertificate572_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate572.chunkCheck r b = true :=
  compactCertificate572.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate572_chunkChecks0
    · exact compactCertificate572_chunkChecks1
    · exact compactCertificate572_chunkChecks2
    · exact compactCertificate572_chunkChecks3
    · exact compactCertificate572_chunkChecks4)

theorem compactCertificate572_coefficient0 :
    compactCertificate572.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate572_coefficient1 :
    compactCertificate572.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate572_coefficient2 :
    compactCertificate572.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate572_coefficient3 :
    compactCertificate572.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate572_coefficient4 :
    compactCertificate572.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate572_coefficients : ∀ r : Fin 5,
    compactCertificate572.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate572_coefficient0
  · exact compactCertificate572_coefficient1
  · exact compactCertificate572_coefficient2
  · exact compactCertificate572_coefficient3
  · exact compactCertificate572_coefficient4

theorem compactCertificate572_lower : (1 : ℚ) ≤ compactCertificate572.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate572, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate572_proves {t : ℝ} (ht : t ∈ compactCertificate572.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate572.proves compactCertificate572_states compactCertificate572_chunks
    compactCertificate572_coefficients compactCertificate572_lower ht

end Erdos232
