/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate523 : CompactCertificate where
  left := 394
  right := 395
  center := 789 / 2
  grid := fun i =>
    match i.val with
    | 0 => 126
    | 1 => 93
    | 2 => 150
    | 3 => 27
    | 4 => 73
    | 5 => 197
    | 6 => 145
    | 7 => 249
    | 8 => 183
    | 9 => 281
    | 10 => 162
    | 11 => 288
    | 12 => 269
    | 13 => 192
    | 14 => 218
    | 15 => 181
    | 16 => 160
    | 17 => 232
    | 18 => 129
    | 19 => 109
    | 20 => 68
    | 21 => 37
    | 22 => 100
    | 23 => 136
    | 24 => 57
    | 25 => 234
    | _ => 156
  point := fun i =>
    match i.val with
    | 0 => 789 / 2
    | 1 => 1162347657893889 / 4000000000000
    | 2 => 375879350623137 / 800000000000
    | 3 => 339170147637123 / 4000000000000
    | 4 => 911058724781031 / 4000000000000
    | 5 => 2473701663942027 / 4000000000000
    | 6 => 1822117449562851 / 4000000000000
    | 7 => 3122229306823023 / 4000000000000
    | 8 => 2299819976039757 / 4000000000000
    | 9 => 3528515268494211 / 4000000000000
    | 10 => 2037189240104619 / 4000000000000
    | 11 => 3615028055821671 / 4000000000000
    | 12 => 3377628138854499 / 4000000000000
    | 13 => 2410434815546067 / 4000000000000
    | 14 => 2733176174343093 / 4000000000000
    | 15 => 2278637346226917 / 4000000000000
    | 16 => 2013245199529257 / 4000000000000
    | 17 => 583516928824443 / 800000000000
    | 18 => 1614038533941921 / 4000000000000
    | 19 => 1368238340209881 / 4000000000000
    | 20 => 856180023960243 / 4000000000000
    | 21 => 460456464411981 / 4000000000000
    | 22 => 1250228872418943 / 4000000000000
    | 23 => 1707080639934111 / 4000000000000
    | 24 => 721819976039757 / 4000000000000
    | 25 => 2934158128354797 / 4000000000000
    | _ => 1959881648929923 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-21188266266 / 1000000000000) (-21188264500 / 1000000000000), orderedInterval (34155966090 / 1000000000000) (34155967855 / 1000000000000))
    | 1 => (orderedInterval (33453528303 / 1000000000000) (33453562841 / 1000000000000), orderedInterval (-32793902846 / 1000000000000) (-32793868308 / 1000000000000))
    | 2 => (orderedInterval (-20923096938 / 1000000000000) (-20923094942 / 1000000000000), orderedInterval (30307067006 / 1000000000000) (30307069001 / 1000000000000))
    | 3 => (orderedInterval (-59281455729 / 1000000000000) (-59281455728 / 1000000000000), orderedInterval (-62846067270 / 1000000000000) (-62846067269 / 1000000000000))
    | 4 => (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))
    | 5 => (orderedInterval (-9997031963 / 1000000000000) (-9997031962 / 1000000000000), orderedInterval (-30479293053 / 1000000000000) (-30479293052 / 1000000000000))
    | 6 => (orderedInterval (-26385371498 / 1000000000000) (-26385371497 / 1000000000000), orderedInterval (-26454062916 / 1000000000000) (-26454062915 / 1000000000000))
    | 7 => (orderedInterval (22617188102 / 1000000000000) (22617198094 / 1000000000000), orderedInterval (-17451779337 / 1000000000000) (-17451769345 / 1000000000000))
    | 8 => (orderedInterval (-24526164832 / 1000000000000) (-24526164831 / 1000000000000), orderedInterval (-22466861258 / 1000000000000) (-22466861257 / 1000000000000))
    | 9 => (orderedInterval (-3390276640 / 1000000000000) (-3390276639 / 1000000000000), orderedInterval (-26647503465 / 1000000000000) (-26647503464 / 1000000000000))
    | 10 => (orderedInterval (32190414793 / 1000000000000) (32190414795 / 1000000000000), orderedInterval (14589380014 / 1000000000000) (14589380016 / 1000000000000))
    | 11 => (orderedInterval (-6216240459 / 1000000000000) (-6216240458 / 1000000000000), orderedInterval (25806020414 / 1000000000000) (25806020415 / 1000000000000))
    | 12 => (orderedInterval (-2846660291 / 1000000000000) (-2846660290 / 1000000000000), orderedInterval (-27308054239 / 1000000000000) (-27308054238 / 1000000000000))
    | 13 => (orderedInterval (6715306119 / 1000000000000) (6715306120 / 1000000000000), orderedInterval (31796074632 / 1000000000000) (31796074633 / 1000000000000))
    | 14 => (orderedInterval (-21638253000 / 1000000000000) (-21638248461 / 1000000000000), orderedInterval (21544379085 / 1000000000000) (21544383624 / 1000000000000))
    | 15 => (orderedInterval (-32427755858 / 1000000000000) (-32427744071 / 1000000000000), orderedInterval (8151592600 / 1000000000000) (8151604387 / 1000000000000))
    | 16 => (orderedInterval (35268610291 / 1000000000000) (35268610388 / 1000000000000), orderedInterval (4546162534 / 1000000000000) (4546162631 / 1000000000000))
    | 17 => (orderedInterval (28704159309 / 1000000000000) (28704159413 / 1000000000000), orderedInterval (6971381597 / 1000000000000) (6971381701 / 1000000000000))
    | 18 => (orderedInterval (32781082663 / 1000000000000) (32781178692 / 1000000000000), orderedInterval (-22470634198 / 1000000000000) (-22470538169 / 1000000000000))
    | 19 => (orderedInterval (-17236645228 / 1000000000000) (-17236645227 / 1000000000000), orderedInterval (-39522705757 / 1000000000000) (-39522705756 / 1000000000000))
    | 20 => (orderedInterval (50860083105 / 1000000000000) (50860083106 / 1000000000000), orderedInterval (19565684756 / 1000000000000) (19565684757 / 1000000000000))
    | 21 => (orderedInterval (24835094662 / 1000000000000) (24835095399 / 1000000000000), orderedInterval (-70204908819 / 1000000000000) (-70204908082 / 1000000000000))
    | 22 => (orderedInterval (-32906362798 / 1000000000000) (-32906325095 / 1000000000000), orderedInterval (30939230671 / 1000000000000) (30939268373 / 1000000000000))
    | 23 => (orderedInterval (11364502951 / 1000000000000) (11364502952 / 1000000000000), orderedInterval (36899619199 / 1000000000000) (36899619200 / 1000000000000))
    | 24 => (orderedInterval (-49084284393 / 1000000000000) (-49084234155 / 1000000000000), orderedInterval (33581294068 / 1000000000000) (33581344306 / 1000000000000))
    | 25 => (orderedInterval (-21295007803 / 1000000000000) (-21295003521 / 1000000000000), orderedInterval (20371245737 / 1000000000000) (20371250020 / 1000000000000))
    | _ => (orderedInterval (22301963027 / 1000000000000) (22301963028 / 1000000000000), orderedInterval (28295523359 / 1000000000000) (28295523360 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-9314356221 / 1000000000000) (-9314355054 / 1000000000000)
      | 1 => orderedInterval (2720608553 / 1000000000000) (2720610141 / 1000000000000)
      | 2 => orderedInterval (-1290353906 / 1000000000000) (-1290353575 / 1000000000000)
      | 3 => orderedInterval (2103780780 / 1000000000000) (2103780937 / 1000000000000)
      | 4 => orderedInterval (795911573 / 1000000000000) (795911643 / 1000000000000)
      | 5 => orderedInterval (-1657830558 / 1000000000000) (-1657830375 / 1000000000000)
      | 6 => orderedInterval (-2610105612 / 1000000000000) (-2610090159 / 1000000000000)
      | 7 => orderedInterval (-583004374 / 1000000000000) (-583003457 / 1000000000000)
      | _ => orderedInterval (-2746884961 / 1000000000000) (-2746884200 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15431280080 / 1000000000000) (15431281188 / 1000000000000)
      | 1 => orderedInterval (2754476126 / 1000000000000) (2754477069 / 1000000000000)
      | 2 => orderedInterval (273691663 / 1000000000000) (273692311 / 1000000000000)
      | 3 => orderedInterval (20387238708 / 1000000000000) (20387239033 / 1000000000000)
      | 4 => orderedInterval (5459242264 / 1000000000000) (5459242381 / 1000000000000)
      | 5 => orderedInterval (134028494 / 1000000000000) (134028757 / 1000000000000)
      | 6 => orderedInterval (5960147954 / 1000000000000) (5960163751 / 1000000000000)
      | 7 => orderedInterval (-3237120219 / 1000000000000) (-3237119494 / 1000000000000)
      | _ => orderedInterval (-9584571828 / 1000000000000) (-9584570888 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9931634155 / 1000000000000) (9931635235 / 1000000000000)
      | 1 => orderedInterval (-2238740137 / 1000000000000) (-2238739546 / 1000000000000)
      | 2 => orderedInterval (3989380887 / 1000000000000) (3989382164 / 1000000000000)
      | 3 => orderedInterval (-2401116666 / 1000000000000) (-2401115970 / 1000000000000)
      | 4 => orderedInterval (-2059503522 / 1000000000000) (-2059503326 / 1000000000000)
      | 5 => orderedInterval (1553330870 / 1000000000000) (1553331254 / 1000000000000)
      | 6 => orderedInterval (4247586649 / 1000000000000) (4247602840 / 1000000000000)
      | 7 => orderedInterval (597913844 / 1000000000000) (597914427 / 1000000000000)
      | _ => orderedInterval (547729882 / 1000000000000) (547731380 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16445713333 / 1000000000000) (-16445712263 / 1000000000000)
      | 1 => orderedInterval (-8085201691 / 1000000000000) (-8085201281 / 1000000000000)
      | 2 => orderedInterval (-2498700499 / 1000000000000) (-2498697984 / 1000000000000)
      | 3 => orderedInterval (-99364086472 / 1000000000000) (-99364084946 / 1000000000000)
      | 4 => orderedInterval (-14979437596 / 1000000000000) (-14979437261 / 1000000000000)
      | 5 => orderedInterval (-875263957 / 1000000000000) (-875263392 / 1000000000000)
      | 6 => orderedInterval (-5415415267 / 1000000000000) (-5415398711 / 1000000000000)
      | 7 => orderedInterval (3895580374 / 1000000000000) (3895580845 / 1000000000000)
      | _ => orderedInterval (20811153459 / 1000000000000) (20811156083 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10693499891 / 1000000000000) (-10693498807 / 1000000000000)
      | 1 => orderedInterval (4486002383 / 1000000000000) (4486002728 / 1000000000000)
      | 2 => orderedInterval (-13353207290 / 1000000000000) (-13353202324 / 1000000000000)
      | 3 => orderedInterval (-2150349143 / 1000000000000) (-2150345755 / 1000000000000)
      | 4 => orderedInterval (5597483627 / 1000000000000) (5597484207 / 1000000000000)
      | 5 => orderedInterval (1617406975 / 1000000000000) (1617407814 / 1000000000000)
      | 6 => orderedInterval (-5014535816 / 1000000000000) (-5014518843 / 1000000000000)
      | 7 => orderedInterval (-921765121 / 1000000000000) (-921764736 / 1000000000000)
      | _ => orderedInterval (10645869210 / 1000000000000) (10645873963 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-12582234726 / 1000000000000) (-12582214099 / 1000000000000)
    | 1 => orderedInterval (37578413242 / 1000000000000) (37578434108 / 1000000000000)
    | 2 => orderedInterval (14168215962 / 1000000000000) (14168238458 / 1000000000000)
    | 3 => orderedInterval (-122957084982 / 1000000000000) (-122957058910 / 1000000000000)
    | _ => orderedInterval (-9786595066 / 1000000000000) (-9786561753 / 1000000000000)

theorem compactCertificate523_stateChecks0 :
    compactCertificate523.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (789 / 2)) (orderedInterval (-21188266266 / 1000000000000) (-21188264500 / 1000000000000), orderedInterval (34155966090 / 1000000000000) (34155967855 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1162347657893889 / 4000000000000)) (orderedInterval (33453528303 / 1000000000000) (33453562841 / 1000000000000), orderedInterval (-32793902846 / 1000000000000) (-32793868308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (375879350623137 / 800000000000)) (orderedInterval (-20923096938 / 1000000000000) (-20923094942 / 1000000000000), orderedInterval (30307067006 / 1000000000000) (30307069001 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks1 :
    compactCertificate523.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (339170147637123 / 4000000000000)) (orderedInterval (-59281455729 / 1000000000000) (-59281455728 / 1000000000000), orderedInterval (-62846067270 / 1000000000000) (-62846067269 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (911058724781031 / 4000000000000)) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2473701663942027 / 4000000000000)) (orderedInterval (-9997031963 / 1000000000000) (-9997031962 / 1000000000000), orderedInterval (-30479293053 / 1000000000000) (-30479293052 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks2 :
    compactCertificate523.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1822117449562851 / 4000000000000)) (orderedInterval (-26385371498 / 1000000000000) (-26385371497 / 1000000000000), orderedInterval (-26454062916 / 1000000000000) (-26454062915 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3122229306823023 / 4000000000000)) (orderedInterval (22617188102 / 1000000000000) (22617198094 / 1000000000000), orderedInterval (-17451779337 / 1000000000000) (-17451769345 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2299819976039757 / 4000000000000)) (orderedInterval (-24526164832 / 1000000000000) (-24526164831 / 1000000000000), orderedInterval (-22466861258 / 1000000000000) (-22466861257 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks3 :
    compactCertificate523.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (3528515268494211 / 4000000000000)) (orderedInterval (-3390276640 / 1000000000000) (-3390276639 / 1000000000000), orderedInterval (-26647503465 / 1000000000000) (-26647503464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2037189240104619 / 4000000000000)) (orderedInterval (32190414793 / 1000000000000) (32190414795 / 1000000000000), orderedInterval (14589380014 / 1000000000000) (14589380016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (3615028055821671 / 4000000000000)) (orderedInterval (-6216240459 / 1000000000000) (-6216240458 / 1000000000000), orderedInterval (25806020414 / 1000000000000) (25806020415 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks4 :
    compactCertificate523.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (3377628138854499 / 4000000000000)) (orderedInterval (-2846660291 / 1000000000000) (-2846660290 / 1000000000000), orderedInterval (-27308054239 / 1000000000000) (-27308054238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2410434815546067 / 4000000000000)) (orderedInterval (6715306119 / 1000000000000) (6715306120 / 1000000000000), orderedInterval (31796074632 / 1000000000000) (31796074633 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2733176174343093 / 4000000000000)) (orderedInterval (-21638253000 / 1000000000000) (-21638248461 / 1000000000000), orderedInterval (21544379085 / 1000000000000) (21544383624 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks5 :
    compactCertificate523.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2278637346226917 / 4000000000000)) (orderedInterval (-32427755858 / 1000000000000) (-32427744071 / 1000000000000), orderedInterval (8151592600 / 1000000000000) (8151604387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2013245199529257 / 4000000000000)) (orderedInterval (35268610291 / 1000000000000) (35268610388 / 1000000000000), orderedInterval (4546162534 / 1000000000000) (4546162631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (583516928824443 / 800000000000)) (orderedInterval (28704159309 / 1000000000000) (28704159413 / 1000000000000), orderedInterval (6971381597 / 1000000000000) (6971381701 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks6 :
    compactCertificate523.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1614038533941921 / 4000000000000)) (orderedInterval (32781082663 / 1000000000000) (32781178692 / 1000000000000), orderedInterval (-22470634198 / 1000000000000) (-22470538169 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1368238340209881 / 4000000000000)) (orderedInterval (-17236645228 / 1000000000000) (-17236645227 / 1000000000000), orderedInterval (-39522705757 / 1000000000000) (-39522705756 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (856180023960243 / 4000000000000)) (orderedInterval (50860083105 / 1000000000000) (50860083106 / 1000000000000), orderedInterval (19565684756 / 1000000000000) (19565684757 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks7 :
    compactCertificate523.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (460456464411981 / 4000000000000)) (orderedInterval (24835094662 / 1000000000000) (24835095399 / 1000000000000), orderedInterval (-70204908819 / 1000000000000) (-70204908082 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1250228872418943 / 4000000000000)) (orderedInterval (-32906362798 / 1000000000000) (-32906325095 / 1000000000000), orderedInterval (30939230671 / 1000000000000) (30939268373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1707080639934111 / 4000000000000)) (orderedInterval (11364502951 / 1000000000000) (11364502952 / 1000000000000), orderedInterval (36899619199 / 1000000000000) (36899619200 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_stateChecks8 :
    compactCertificate523.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (721819976039757 / 4000000000000)) (orderedInterval (-49084284393 / 1000000000000) (-49084234155 / 1000000000000), orderedInterval (33581294068 / 1000000000000) (33581344306 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2934158128354797 / 4000000000000)) (orderedInterval (-21295007803 / 1000000000000) (-21295003521 / 1000000000000), orderedInterval (20371245737 / 1000000000000) (20371250020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1959881648929923 / 4000000000000)) (orderedInterval (22301963027 / 1000000000000) (22301963028 / 1000000000000), orderedInterval (28295523359 / 1000000000000) (28295523360 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_states : ∀ j,
    BesselStateValid (compactCertificate523.point j) (compactCertificate523.state j) :=
  compactCertificate523.statesValid_of_checks3 compactCertificate523_stateChecks0
    compactCertificate523_stateChecks1 compactCertificate523_stateChecks2
    compactCertificate523_stateChecks3 compactCertificate523_stateChecks4
    compactCertificate523_stateChecks5 compactCertificate523_stateChecks6
    compactCertificate523_stateChecks7 compactCertificate523_stateChecks8

theorem compactCertificate523_chunkChecks0_0 :
    compactCertificate523.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (789 / 2) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21188266266 / 1000000000000) (-21188264500 / 1000000000000), orderedInterval (34155966090 / 1000000000000) (34155967855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1162347657893889 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33453528303 / 1000000000000) (33453562841 / 1000000000000), orderedInterval (-32793902846 / 1000000000000) (-32793868308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (375879350623137 / 800000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20923096938 / 1000000000000) (-20923094942 / 1000000000000), orderedInterval (30307067006 / 1000000000000) (30307069001 / 1000000000000)))) (orderedInterval (-9314356221 / 1000000000000) (-9314355054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (339170147637123 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59281455729 / 1000000000000) (-59281455728 / 1000000000000), orderedInterval (-62846067270 / 1000000000000) (-62846067269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2473701663942027 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9997031963 / 1000000000000) (-9997031962 / 1000000000000), orderedInterval (-30479293053 / 1000000000000) (-30479293052 / 1000000000000)))) (orderedInterval (2720608553 / 1000000000000) (2720610141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1822117449562851 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26385371498 / 1000000000000) (-26385371497 / 1000000000000), orderedInterval (-26454062916 / 1000000000000) (-26454062915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3122229306823023 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22617188102 / 1000000000000) (22617198094 / 1000000000000), orderedInterval (-17451779337 / 1000000000000) (-17451769345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2299819976039757 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24526164832 / 1000000000000) (-24526164831 / 1000000000000), orderedInterval (-22466861258 / 1000000000000) (-22466861257 / 1000000000000)))) (orderedInterval (-1290353906 / 1000000000000) (-1290353575 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks0_1 :
    compactCertificate523.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3528515268494211 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3390276640 / 1000000000000) (-3390276639 / 1000000000000), orderedInterval (-26647503465 / 1000000000000) (-26647503464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2037189240104619 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32190414793 / 1000000000000) (32190414795 / 1000000000000), orderedInterval (14589380014 / 1000000000000) (14589380016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3615028055821671 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6216240459 / 1000000000000) (-6216240458 / 1000000000000), orderedInterval (25806020414 / 1000000000000) (25806020415 / 1000000000000)))) (orderedInterval (2103780780 / 1000000000000) (2103780937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3377628138854499 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2846660291 / 1000000000000) (-2846660290 / 1000000000000), orderedInterval (-27308054239 / 1000000000000) (-27308054238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2410434815546067 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6715306119 / 1000000000000) (6715306120 / 1000000000000), orderedInterval (31796074632 / 1000000000000) (31796074633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2733176174343093 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21638253000 / 1000000000000) (-21638248461 / 1000000000000), orderedInterval (21544379085 / 1000000000000) (21544383624 / 1000000000000)))) (orderedInterval (795911573 / 1000000000000) (795911643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2278637346226917 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32427755858 / 1000000000000) (-32427744071 / 1000000000000), orderedInterval (8151592600 / 1000000000000) (8151604387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2013245199529257 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35268610291 / 1000000000000) (35268610388 / 1000000000000), orderedInterval (4546162534 / 1000000000000) (4546162631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (583516928824443 / 800000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28704159309 / 1000000000000) (28704159413 / 1000000000000), orderedInterval (6971381597 / 1000000000000) (6971381701 / 1000000000000)))) (orderedInterval (-1657830558 / 1000000000000) (-1657830375 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks0_2 :
    compactCertificate523.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1614038533941921 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32781082663 / 1000000000000) (32781178692 / 1000000000000), orderedInterval (-22470634198 / 1000000000000) (-22470538169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1368238340209881 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17236645228 / 1000000000000) (-17236645227 / 1000000000000), orderedInterval (-39522705757 / 1000000000000) (-39522705756 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (856180023960243 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50860083105 / 1000000000000) (50860083106 / 1000000000000), orderedInterval (19565684756 / 1000000000000) (19565684757 / 1000000000000)))) (orderedInterval (-2610105612 / 1000000000000) (-2610090159 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (460456464411981 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24835094662 / 1000000000000) (24835095399 / 1000000000000), orderedInterval (-70204908819 / 1000000000000) (-70204908082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1250228872418943 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32906362798 / 1000000000000) (-32906325095 / 1000000000000), orderedInterval (30939230671 / 1000000000000) (30939268373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1707080639934111 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11364502951 / 1000000000000) (11364502952 / 1000000000000), orderedInterval (36899619199 / 1000000000000) (36899619200 / 1000000000000)))) (orderedInterval (-583004374 / 1000000000000) (-583003457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (721819976039757 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49084284393 / 1000000000000) (-49084234155 / 1000000000000), orderedInterval (33581294068 / 1000000000000) (33581344306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2934158128354797 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21295007803 / 1000000000000) (-21295003521 / 1000000000000), orderedInterval (20371245737 / 1000000000000) (20371250020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1959881648929923 / 4000000000000) 0 (IntervalRat.scale (789 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22301963027 / 1000000000000) (22301963028 / 1000000000000), orderedInterval (28295523359 / 1000000000000) (28295523360 / 1000000000000)))) (orderedInterval (-2746884961 / 1000000000000) (-2746884200 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks0 :
    compactCertificate523.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate523.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate523_chunkChecks0_0
    compactCertificate523_chunkChecks0_1 compactCertificate523_chunkChecks0_2

theorem compactCertificate523_chunkChecks1_0 :
    compactCertificate523.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (789 / 2) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21188266266 / 1000000000000) (-21188264500 / 1000000000000), orderedInterval (34155966090 / 1000000000000) (34155967855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1162347657893889 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33453528303 / 1000000000000) (33453562841 / 1000000000000), orderedInterval (-32793902846 / 1000000000000) (-32793868308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (375879350623137 / 800000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20923096938 / 1000000000000) (-20923094942 / 1000000000000), orderedInterval (30307067006 / 1000000000000) (30307069001 / 1000000000000)))) (orderedInterval (15431280080 / 1000000000000) (15431281188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (339170147637123 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59281455729 / 1000000000000) (-59281455728 / 1000000000000), orderedInterval (-62846067270 / 1000000000000) (-62846067269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2473701663942027 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9997031963 / 1000000000000) (-9997031962 / 1000000000000), orderedInterval (-30479293053 / 1000000000000) (-30479293052 / 1000000000000)))) (orderedInterval (2754476126 / 1000000000000) (2754477069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1822117449562851 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26385371498 / 1000000000000) (-26385371497 / 1000000000000), orderedInterval (-26454062916 / 1000000000000) (-26454062915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3122229306823023 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22617188102 / 1000000000000) (22617198094 / 1000000000000), orderedInterval (-17451779337 / 1000000000000) (-17451769345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2299819976039757 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24526164832 / 1000000000000) (-24526164831 / 1000000000000), orderedInterval (-22466861258 / 1000000000000) (-22466861257 / 1000000000000)))) (orderedInterval (273691663 / 1000000000000) (273692311 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks1_1 :
    compactCertificate523.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3528515268494211 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3390276640 / 1000000000000) (-3390276639 / 1000000000000), orderedInterval (-26647503465 / 1000000000000) (-26647503464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2037189240104619 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32190414793 / 1000000000000) (32190414795 / 1000000000000), orderedInterval (14589380014 / 1000000000000) (14589380016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3615028055821671 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6216240459 / 1000000000000) (-6216240458 / 1000000000000), orderedInterval (25806020414 / 1000000000000) (25806020415 / 1000000000000)))) (orderedInterval (20387238708 / 1000000000000) (20387239033 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3377628138854499 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2846660291 / 1000000000000) (-2846660290 / 1000000000000), orderedInterval (-27308054239 / 1000000000000) (-27308054238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2410434815546067 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6715306119 / 1000000000000) (6715306120 / 1000000000000), orderedInterval (31796074632 / 1000000000000) (31796074633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2733176174343093 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21638253000 / 1000000000000) (-21638248461 / 1000000000000), orderedInterval (21544379085 / 1000000000000) (21544383624 / 1000000000000)))) (orderedInterval (5459242264 / 1000000000000) (5459242381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2278637346226917 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32427755858 / 1000000000000) (-32427744071 / 1000000000000), orderedInterval (8151592600 / 1000000000000) (8151604387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2013245199529257 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35268610291 / 1000000000000) (35268610388 / 1000000000000), orderedInterval (4546162534 / 1000000000000) (4546162631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (583516928824443 / 800000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28704159309 / 1000000000000) (28704159413 / 1000000000000), orderedInterval (6971381597 / 1000000000000) (6971381701 / 1000000000000)))) (orderedInterval (134028494 / 1000000000000) (134028757 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks1_2 :
    compactCertificate523.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1614038533941921 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32781082663 / 1000000000000) (32781178692 / 1000000000000), orderedInterval (-22470634198 / 1000000000000) (-22470538169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1368238340209881 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17236645228 / 1000000000000) (-17236645227 / 1000000000000), orderedInterval (-39522705757 / 1000000000000) (-39522705756 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (856180023960243 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50860083105 / 1000000000000) (50860083106 / 1000000000000), orderedInterval (19565684756 / 1000000000000) (19565684757 / 1000000000000)))) (orderedInterval (5960147954 / 1000000000000) (5960163751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (460456464411981 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24835094662 / 1000000000000) (24835095399 / 1000000000000), orderedInterval (-70204908819 / 1000000000000) (-70204908082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1250228872418943 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32906362798 / 1000000000000) (-32906325095 / 1000000000000), orderedInterval (30939230671 / 1000000000000) (30939268373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1707080639934111 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11364502951 / 1000000000000) (11364502952 / 1000000000000), orderedInterval (36899619199 / 1000000000000) (36899619200 / 1000000000000)))) (orderedInterval (-3237120219 / 1000000000000) (-3237119494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (721819976039757 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49084284393 / 1000000000000) (-49084234155 / 1000000000000), orderedInterval (33581294068 / 1000000000000) (33581344306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2934158128354797 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21295007803 / 1000000000000) (-21295003521 / 1000000000000), orderedInterval (20371245737 / 1000000000000) (20371250020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1959881648929923 / 4000000000000) 1 (IntervalRat.scale (789 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22301963027 / 1000000000000) (22301963028 / 1000000000000), orderedInterval (28295523359 / 1000000000000) (28295523360 / 1000000000000)))) (orderedInterval (-9584571828 / 1000000000000) (-9584570888 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks1 :
    compactCertificate523.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate523.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate523_chunkChecks1_0
    compactCertificate523_chunkChecks1_1 compactCertificate523_chunkChecks1_2

theorem compactCertificate523_chunkChecks2_0 :
    compactCertificate523.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (789 / 2) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21188266266 / 1000000000000) (-21188264500 / 1000000000000), orderedInterval (34155966090 / 1000000000000) (34155967855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1162347657893889 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33453528303 / 1000000000000) (33453562841 / 1000000000000), orderedInterval (-32793902846 / 1000000000000) (-32793868308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (375879350623137 / 800000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20923096938 / 1000000000000) (-20923094942 / 1000000000000), orderedInterval (30307067006 / 1000000000000) (30307069001 / 1000000000000)))) (orderedInterval (9931634155 / 1000000000000) (9931635235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (339170147637123 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59281455729 / 1000000000000) (-59281455728 / 1000000000000), orderedInterval (-62846067270 / 1000000000000) (-62846067269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2473701663942027 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9997031963 / 1000000000000) (-9997031962 / 1000000000000), orderedInterval (-30479293053 / 1000000000000) (-30479293052 / 1000000000000)))) (orderedInterval (-2238740137 / 1000000000000) (-2238739546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1822117449562851 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26385371498 / 1000000000000) (-26385371497 / 1000000000000), orderedInterval (-26454062916 / 1000000000000) (-26454062915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3122229306823023 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22617188102 / 1000000000000) (22617198094 / 1000000000000), orderedInterval (-17451779337 / 1000000000000) (-17451769345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2299819976039757 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24526164832 / 1000000000000) (-24526164831 / 1000000000000), orderedInterval (-22466861258 / 1000000000000) (-22466861257 / 1000000000000)))) (orderedInterval (3989380887 / 1000000000000) (3989382164 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks2_1 :
    compactCertificate523.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3528515268494211 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3390276640 / 1000000000000) (-3390276639 / 1000000000000), orderedInterval (-26647503465 / 1000000000000) (-26647503464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2037189240104619 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32190414793 / 1000000000000) (32190414795 / 1000000000000), orderedInterval (14589380014 / 1000000000000) (14589380016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3615028055821671 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6216240459 / 1000000000000) (-6216240458 / 1000000000000), orderedInterval (25806020414 / 1000000000000) (25806020415 / 1000000000000)))) (orderedInterval (-2401116666 / 1000000000000) (-2401115970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3377628138854499 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2846660291 / 1000000000000) (-2846660290 / 1000000000000), orderedInterval (-27308054239 / 1000000000000) (-27308054238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2410434815546067 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6715306119 / 1000000000000) (6715306120 / 1000000000000), orderedInterval (31796074632 / 1000000000000) (31796074633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2733176174343093 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21638253000 / 1000000000000) (-21638248461 / 1000000000000), orderedInterval (21544379085 / 1000000000000) (21544383624 / 1000000000000)))) (orderedInterval (-2059503522 / 1000000000000) (-2059503326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2278637346226917 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32427755858 / 1000000000000) (-32427744071 / 1000000000000), orderedInterval (8151592600 / 1000000000000) (8151604387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2013245199529257 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35268610291 / 1000000000000) (35268610388 / 1000000000000), orderedInterval (4546162534 / 1000000000000) (4546162631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (583516928824443 / 800000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28704159309 / 1000000000000) (28704159413 / 1000000000000), orderedInterval (6971381597 / 1000000000000) (6971381701 / 1000000000000)))) (orderedInterval (1553330870 / 1000000000000) (1553331254 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks2_2 :
    compactCertificate523.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1614038533941921 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32781082663 / 1000000000000) (32781178692 / 1000000000000), orderedInterval (-22470634198 / 1000000000000) (-22470538169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1368238340209881 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17236645228 / 1000000000000) (-17236645227 / 1000000000000), orderedInterval (-39522705757 / 1000000000000) (-39522705756 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (856180023960243 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50860083105 / 1000000000000) (50860083106 / 1000000000000), orderedInterval (19565684756 / 1000000000000) (19565684757 / 1000000000000)))) (orderedInterval (4247586649 / 1000000000000) (4247602840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (460456464411981 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24835094662 / 1000000000000) (24835095399 / 1000000000000), orderedInterval (-70204908819 / 1000000000000) (-70204908082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1250228872418943 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32906362798 / 1000000000000) (-32906325095 / 1000000000000), orderedInterval (30939230671 / 1000000000000) (30939268373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1707080639934111 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11364502951 / 1000000000000) (11364502952 / 1000000000000), orderedInterval (36899619199 / 1000000000000) (36899619200 / 1000000000000)))) (orderedInterval (597913844 / 1000000000000) (597914427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (721819976039757 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49084284393 / 1000000000000) (-49084234155 / 1000000000000), orderedInterval (33581294068 / 1000000000000) (33581344306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2934158128354797 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21295007803 / 1000000000000) (-21295003521 / 1000000000000), orderedInterval (20371245737 / 1000000000000) (20371250020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1959881648929923 / 4000000000000) 2 (IntervalRat.scale (789 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22301963027 / 1000000000000) (22301963028 / 1000000000000), orderedInterval (28295523359 / 1000000000000) (28295523360 / 1000000000000)))) (orderedInterval (547729882 / 1000000000000) (547731380 / 1000000000000))) = true
  rfl'

theorem compactCertificate523_chunkChecks2 :
    compactCertificate523.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate523.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate523_chunkChecks2_0
    compactCertificate523_chunkChecks2_1 compactCertificate523_chunkChecks2_2

theorem compactCertificate523_chunkChecks3_0 :
    compactCertificate523.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (789 / 2) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21188266266 / 1000000000000) (-21188264500 / 1000000000000), orderedInterval (34155966090 / 1000000000000) (34155967855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1162347657893889 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33453528303 / 1000000000000) (33453562841 / 1000000000000), orderedInterval (-32793902846 / 1000000000000) (-32793868308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (375879350623137 / 800000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20923096938 / 1000000000000) (-20923094942 / 1000000000000), orderedInterval (30307067006 / 1000000000000) (30307069001 / 1000000000000)))) (orderedInterval (-16445713333 / 1000000000000) (-16445712263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (339170147637123 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59281455729 / 1000000000000) (-59281455728 / 1000000000000), orderedInterval (-62846067270 / 1000000000000) (-62846067269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2473701663942027 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9997031963 / 1000000000000) (-9997031962 / 1000000000000), orderedInterval (-30479293053 / 1000000000000) (-30479293052 / 1000000000000)))) (orderedInterval (-8085201691 / 1000000000000) (-8085201281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1822117449562851 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26385371498 / 1000000000000) (-26385371497 / 1000000000000), orderedInterval (-26454062916 / 1000000000000) (-26454062915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3122229306823023 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22617188102 / 1000000000000) (22617198094 / 1000000000000), orderedInterval (-17451779337 / 1000000000000) (-17451769345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2299819976039757 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24526164832 / 1000000000000) (-24526164831 / 1000000000000), orderedInterval (-22466861258 / 1000000000000) (-22466861257 / 1000000000000)))) (orderedInterval (-2498700499 / 1000000000000) (-2498697984 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate523_chunkChecks3_1 :
    compactCertificate523.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3528515268494211 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3390276640 / 1000000000000) (-3390276639 / 1000000000000), orderedInterval (-26647503465 / 1000000000000) (-26647503464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2037189240104619 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32190414793 / 1000000000000) (32190414795 / 1000000000000), orderedInterval (14589380014 / 1000000000000) (14589380016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3615028055821671 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6216240459 / 1000000000000) (-6216240458 / 1000000000000), orderedInterval (25806020414 / 1000000000000) (25806020415 / 1000000000000)))) (orderedInterval (-99364086472 / 1000000000000) (-99364084946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3377628138854499 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2846660291 / 1000000000000) (-2846660290 / 1000000000000), orderedInterval (-27308054239 / 1000000000000) (-27308054238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2410434815546067 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6715306119 / 1000000000000) (6715306120 / 1000000000000), orderedInterval (31796074632 / 1000000000000) (31796074633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2733176174343093 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21638253000 / 1000000000000) (-21638248461 / 1000000000000), orderedInterval (21544379085 / 1000000000000) (21544383624 / 1000000000000)))) (orderedInterval (-14979437596 / 1000000000000) (-14979437261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2278637346226917 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32427755858 / 1000000000000) (-32427744071 / 1000000000000), orderedInterval (8151592600 / 1000000000000) (8151604387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2013245199529257 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35268610291 / 1000000000000) (35268610388 / 1000000000000), orderedInterval (4546162534 / 1000000000000) (4546162631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (583516928824443 / 800000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28704159309 / 1000000000000) (28704159413 / 1000000000000), orderedInterval (6971381597 / 1000000000000) (6971381701 / 1000000000000)))) (orderedInterval (-875263957 / 1000000000000) (-875263392 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate523_chunkChecks3_2 :
    compactCertificate523.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1614038533941921 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32781082663 / 1000000000000) (32781178692 / 1000000000000), orderedInterval (-22470634198 / 1000000000000) (-22470538169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1368238340209881 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17236645228 / 1000000000000) (-17236645227 / 1000000000000), orderedInterval (-39522705757 / 1000000000000) (-39522705756 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (856180023960243 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50860083105 / 1000000000000) (50860083106 / 1000000000000), orderedInterval (19565684756 / 1000000000000) (19565684757 / 1000000000000)))) (orderedInterval (-5415415267 / 1000000000000) (-5415398711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (460456464411981 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24835094662 / 1000000000000) (24835095399 / 1000000000000), orderedInterval (-70204908819 / 1000000000000) (-70204908082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1250228872418943 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32906362798 / 1000000000000) (-32906325095 / 1000000000000), orderedInterval (30939230671 / 1000000000000) (30939268373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1707080639934111 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11364502951 / 1000000000000) (11364502952 / 1000000000000), orderedInterval (36899619199 / 1000000000000) (36899619200 / 1000000000000)))) (orderedInterval (3895580374 / 1000000000000) (3895580845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (721819976039757 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49084284393 / 1000000000000) (-49084234155 / 1000000000000), orderedInterval (33581294068 / 1000000000000) (33581344306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2934158128354797 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21295007803 / 1000000000000) (-21295003521 / 1000000000000), orderedInterval (20371245737 / 1000000000000) (20371250020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1959881648929923 / 4000000000000) 3 (IntervalRat.scale (789 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22301963027 / 1000000000000) (22301963028 / 1000000000000), orderedInterval (28295523359 / 1000000000000) (28295523360 / 1000000000000)))) (orderedInterval (20811153459 / 1000000000000) (20811156083 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate523_chunkChecks3 :
    compactCertificate523.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate523.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate523_chunkChecks3_0
    compactCertificate523_chunkChecks3_1 compactCertificate523_chunkChecks3_2

theorem compactCertificate523_chunkChecks4_0 :
    compactCertificate523.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (789 / 2) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21188266266 / 1000000000000) (-21188264500 / 1000000000000), orderedInterval (34155966090 / 1000000000000) (34155967855 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1162347657893889 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (33453528303 / 1000000000000) (33453562841 / 1000000000000), orderedInterval (-32793902846 / 1000000000000) (-32793868308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (375879350623137 / 800000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20923096938 / 1000000000000) (-20923094942 / 1000000000000), orderedInterval (30307067006 / 1000000000000) (30307069001 / 1000000000000)))) (orderedInterval (-10693499891 / 1000000000000) (-10693498807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (339170147637123 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-59281455729 / 1000000000000) (-59281455728 / 1000000000000), orderedInterval (-62846067270 / 1000000000000) (-62846067269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (911058724781031 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (37433471393 / 1000000000000) (37433513583 / 1000000000000), orderedInterval (-37415965271 / 1000000000000) (-37415923080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2473701663942027 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9997031963 / 1000000000000) (-9997031962 / 1000000000000), orderedInterval (-30479293053 / 1000000000000) (-30479293052 / 1000000000000)))) (orderedInterval (4486002383 / 1000000000000) (4486002728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1822117449562851 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26385371498 / 1000000000000) (-26385371497 / 1000000000000), orderedInterval (-26454062916 / 1000000000000) (-26454062915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3122229306823023 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22617188102 / 1000000000000) (22617198094 / 1000000000000), orderedInterval (-17451779337 / 1000000000000) (-17451769345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2299819976039757 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24526164832 / 1000000000000) (-24526164831 / 1000000000000), orderedInterval (-22466861258 / 1000000000000) (-22466861257 / 1000000000000)))) (orderedInterval (-13353207290 / 1000000000000) (-13353202324 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate523_chunkChecks4_1 :
    compactCertificate523.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3528515268494211 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3390276640 / 1000000000000) (-3390276639 / 1000000000000), orderedInterval (-26647503465 / 1000000000000) (-26647503464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2037189240104619 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32190414793 / 1000000000000) (32190414795 / 1000000000000), orderedInterval (14589380014 / 1000000000000) (14589380016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3615028055821671 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6216240459 / 1000000000000) (-6216240458 / 1000000000000), orderedInterval (25806020414 / 1000000000000) (25806020415 / 1000000000000)))) (orderedInterval (-2150349143 / 1000000000000) (-2150345755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3377628138854499 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2846660291 / 1000000000000) (-2846660290 / 1000000000000), orderedInterval (-27308054239 / 1000000000000) (-27308054238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2410434815546067 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6715306119 / 1000000000000) (6715306120 / 1000000000000), orderedInterval (31796074632 / 1000000000000) (31796074633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2733176174343093 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21638253000 / 1000000000000) (-21638248461 / 1000000000000), orderedInterval (21544379085 / 1000000000000) (21544383624 / 1000000000000)))) (orderedInterval (5597483627 / 1000000000000) (5597484207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2278637346226917 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32427755858 / 1000000000000) (-32427744071 / 1000000000000), orderedInterval (8151592600 / 1000000000000) (8151604387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2013245199529257 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35268610291 / 1000000000000) (35268610388 / 1000000000000), orderedInterval (4546162534 / 1000000000000) (4546162631 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (583516928824443 / 800000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28704159309 / 1000000000000) (28704159413 / 1000000000000), orderedInterval (6971381597 / 1000000000000) (6971381701 / 1000000000000)))) (orderedInterval (1617406975 / 1000000000000) (1617407814 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate523_chunkChecks4_2 :
    compactCertificate523.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1614038533941921 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32781082663 / 1000000000000) (32781178692 / 1000000000000), orderedInterval (-22470634198 / 1000000000000) (-22470538169 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1368238340209881 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17236645228 / 1000000000000) (-17236645227 / 1000000000000), orderedInterval (-39522705757 / 1000000000000) (-39522705756 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (856180023960243 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50860083105 / 1000000000000) (50860083106 / 1000000000000), orderedInterval (19565684756 / 1000000000000) (19565684757 / 1000000000000)))) (orderedInterval (-5014535816 / 1000000000000) (-5014518843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (460456464411981 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24835094662 / 1000000000000) (24835095399 / 1000000000000), orderedInterval (-70204908819 / 1000000000000) (-70204908082 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1250228872418943 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32906362798 / 1000000000000) (-32906325095 / 1000000000000), orderedInterval (30939230671 / 1000000000000) (30939268373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1707080639934111 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11364502951 / 1000000000000) (11364502952 / 1000000000000), orderedInterval (36899619199 / 1000000000000) (36899619200 / 1000000000000)))) (orderedInterval (-921765121 / 1000000000000) (-921764736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (721819976039757 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49084284393 / 1000000000000) (-49084234155 / 1000000000000), orderedInterval (33581294068 / 1000000000000) (33581344306 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2934158128354797 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21295007803 / 1000000000000) (-21295003521 / 1000000000000), orderedInterval (20371245737 / 1000000000000) (20371250020 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1959881648929923 / 4000000000000) 4 (IntervalRat.scale (789 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22301963027 / 1000000000000) (22301963028 / 1000000000000), orderedInterval (28295523359 / 1000000000000) (28295523360 / 1000000000000)))) (orderedInterval (10645869210 / 1000000000000) (10645873963 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate523_chunkChecks4 :
    compactCertificate523.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate523.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate523_chunkChecks4_0
    compactCertificate523_chunkChecks4_1 compactCertificate523_chunkChecks4_2

theorem compactCertificate523_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate523.chunkCheck r b = true :=
  compactCertificate523.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate523_chunkChecks0
    · exact compactCertificate523_chunkChecks1
    · exact compactCertificate523_chunkChecks2
    · exact compactCertificate523_chunkChecks3
    · exact compactCertificate523_chunkChecks4)

theorem compactCertificate523_coefficient0 :
    compactCertificate523.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate523_coefficient1 :
    compactCertificate523.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate523_coefficient2 :
    compactCertificate523.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate523_coefficient3 :
    compactCertificate523.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate523_coefficient4 :
    compactCertificate523.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate523_coefficients : ∀ r : Fin 5,
    compactCertificate523.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate523_coefficient0
  · exact compactCertificate523_coefficient1
  · exact compactCertificate523_coefficient2
  · exact compactCertificate523_coefficient3
  · exact compactCertificate523_coefficient4

theorem compactCertificate523_lower : (1 : ℚ) ≤ compactCertificate523.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate523, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate523_proves {t : ℝ} (ht : t ∈ compactCertificate523.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate523.proves compactCertificate523_states compactCertificate523_chunks
    compactCertificate523_coefficients compactCertificate523_lower ht

end Erdos232
