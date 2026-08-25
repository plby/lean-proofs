/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate282 : CompactCertificate where
  left := 156
  right := 157
  center := 313 / 2
  grid := fun i =>
    match i.val with
    | 0 => 50
    | 1 => 37
    | 2 => 59
    | 3 => 11
    | 4 => 29
    | 5 => 78
    | 6 => 58
    | 7 => 99
    | 8 => 73
    | 9 => 111
    | 10 => 64
    | 11 => 114
    | 12 => 107
    | 13 => 76
    | 14 => 86
    | 15 => 72
    | 16 => 64
    | 17 => 92
    | 18 => 51
    | 19 => 43
    | 20 => 27
    | 21 => 15
    | 22 => 39
    | 23 => 54
    | 24 => 23
    | 25 => 93
    | _ => 62
  point := fun i =>
    match i.val with
    | 0 => 313 / 2
    | 1 => 461108766693013 / 4000000000000
    | 2 => 149113101071029 / 800000000000
    | 3 => 134550388099391 / 4000000000000
    | 4 => 361421268512627 / 4000000000000
    | 5 => 981329050461159 / 4000000000000
    | 6 => 722842537025567 / 4000000000000
    | 7 => 1238603007649691 / 4000000000000
    | 8 => 912349369455569 / 4000000000000
    | 9 => 1399778553914687 / 4000000000000
    | 10 => 808162524908423 / 4000000000000
    | 11 => 1434098582347507 / 4000000000000
    | 12 => 1339920922004383 / 4000000000000
    | 13 => 956230795013839 / 4000000000000
    | 14 => 1084263805537881 / 4000000000000
    | 15 => 903946120873289 / 4000000000000
    | 16 => 798663811727069 / 4000000000000
    | 17 => 231483902055831 / 800000000000
    | 18 => 640296655416757 / 4000000000000
    | 19 => 542786565888077 / 4000000000000
    | 20 => 339650630544431 / 4000000000000
    | 21 => 182665238733777 / 4000000000000
    | 22 => 495971656612331 / 4000000000000
    | 23 => 677206895182987 / 4000000000000
    | 24 => 286349369455569 / 4000000000000
    | 25 => 1163994289195249 / 4000000000000
    | _ => 777494240956991 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (12981357295 / 1000000000000) (12981357296 / 1000000000000), orderedInterval (62403393103 / 1000000000000) (62403393104 / 1000000000000))
    | 1 => (orderedInterval (13115790472 / 1000000000000) (13115790558 / 1000000000000), orderedInterval (-73204256045 / 1000000000000) (-73204255959 / 1000000000000))
    | 2 => (orderedInterval (-56605910294 / 1000000000000) (-56605908694 / 1000000000000), orderedInterval (14686643939 / 1000000000000) (14686645538 / 1000000000000))
    | 3 => (orderedInterval (18956063126 / 1000000000000) (18956063211 / 1000000000000), orderedInterval (-136548049503 / 1000000000000) (-136548049418 / 1000000000000))
    | 4 => (orderedInterval (-2781623603 / 1000000000000) (-2781623598 / 1000000000000), orderedInterval (-83878033459 / 1000000000000) (-83878033455 / 1000000000000))
    | 5 => (orderedInterval (44756267406 / 1000000000000) (44756267407 / 1000000000000), orderedInterval (24235775377 / 1000000000000) (24235775378 / 1000000000000))
    | 6 => (orderedInterval (-39004337005 / 1000000000000) (-39004309203 / 1000000000000), orderedInterval (44846398761 / 1000000000000) (44846426562 / 1000000000000))
    | 7 => (orderedInterval (24921686330 / 1000000000000) (24921690128 / 1000000000000), orderedInterval (-37919510835 / 1000000000000) (-37919507037 / 1000000000000))
    | 8 => (orderedInterval (23646761674 / 1000000000000) (23646763297 / 1000000000000), orderedInterval (-47295434014 / 1000000000000) (-47295432391 / 1000000000000))
    | 9 => (orderedInterval (-38551338928 / 1000000000000) (-38551312314 / 1000000000000), orderedInterval (18303231766 / 1000000000000) (18303258379 / 1000000000000))
    | 10 => (orderedInterval (55094411543 / 1000000000000) (55094412424 / 1000000000000), orderedInterval (-10885579806 / 1000000000000) (-10885578924 / 1000000000000))
    | 11 => (orderedInterval (38768393907 / 1000000000000) (38768393908 / 1000000000000), orderedInterval (16458829631 / 1000000000000) (16458829632 / 1000000000000))
    | 12 => (orderedInterval (16378657844 / 1000000000000) (16378658165 / 1000000000000), orderedInterval (-40425075564 / 1000000000000) (-40425075242 / 1000000000000))
    | 13 => (orderedInterval (45550276960 / 1000000000000) (45550276961 / 1000000000000), orderedInterval (24157712643 / 1000000000000) (24157712644 / 1000000000000))
    | 14 => (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))
    | 15 => (orderedInterval (28940444558 / 1000000000000) (28940444559 / 1000000000000), orderedInterval (44427799799 / 1000000000000) (44427799800 / 1000000000000))
    | 16 => (orderedInterval (-32403300499 / 1000000000000) (-32403291334 / 1000000000000), orderedInterval (46324560695 / 1000000000000) (46324569860 / 1000000000000))
    | 17 => (orderedInterval (42082255054 / 1000000000000) (42082255055 / 1000000000000), orderedInterval (20644829346 / 1000000000000) (20644829347 / 1000000000000))
    | 18 => (orderedInterval (-37537514965 / 1000000000000) (-37537514964 / 1000000000000), orderedInterval (-50557900007 / 1000000000000) (-50557900006 / 1000000000000))
    | 19 => (orderedInterval (-67410049313 / 1000000000000) (-67410049310 / 1000000000000), orderedInterval (-11890311862 / 1000000000000) (-11890311859 / 1000000000000))
    | 20 => (orderedInterval (-66380130159 / 1000000000000) (-66380130158 / 1000000000000), orderedInterval (-55205937725 / 1000000000000) (-55205937724 / 1000000000000))
    | 21 => (orderedInterval (73772318823 / 1000000000000) (73772353551 / 1000000000000), orderedInterval (-92995032605 / 1000000000000) (-92994997876 / 1000000000000))
    | 22 => (orderedInterval (-55517631521 / 1000000000000) (-55517548634 / 1000000000000), orderedInterval (45524074203 / 1000000000000) (45524157090 / 1000000000000))
    | 23 => (orderedInterval (26140085683 / 1000000000000) (26140085684 / 1000000000000), orderedInterval (55393278473 / 1000000000000) (55393278474 / 1000000000000))
    | 24 => (orderedInterval (-10761112784 / 1000000000000) (-10761112782 / 1000000000000), orderedInterval (-93612191949 / 1000000000000) (-93612191947 / 1000000000000))
    | 25 => (orderedInterval (17547603273 / 1000000000000) (17547603697 / 1000000000000), orderedInterval (-43386712891 / 1000000000000) (-43386712467 / 1000000000000))
    | _ => (orderedInterval (21204819112 / 1000000000000) (21204819113 / 1000000000000), orderedInterval (53101845982 / 1000000000000) (53101845983 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1945869963 / 1000000000000) (1945870070 / 1000000000000)
      | 1 => orderedInterval (-3488928773 / 1000000000000) (-3488928752 / 1000000000000)
      | 2 => orderedInterval (-197189065 / 1000000000000) (-197188899 / 1000000000000)
      | 3 => orderedInterval (16443300839 / 1000000000000) (16443305696 / 1000000000000)
      | 4 => orderedInterval (3767736157 / 1000000000000) (3767736185 / 1000000000000)
      | 5 => orderedInterval (3265999337 / 1000000000000) (3265999877 / 1000000000000)
      | 6 => orderedInterval (7656347613 / 1000000000000) (7656347653 / 1000000000000)
      | 7 => orderedInterval (-2106042813 / 1000000000000) (-2106040272 / 1000000000000)
      | _ => orderedInterval (-5471864228 / 1000000000000) (-5471864150 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (25258510413 / 1000000000000) (25258510538 / 1000000000000)
      | 1 => orderedInterval (-4150605880 / 1000000000000) (-4150605858 / 1000000000000)
      | 2 => orderedInterval (648254715 / 1000000000000) (648255020 / 1000000000000)
      | 3 => orderedInterval (-2953474985 / 1000000000000) (-2953464197 / 1000000000000)
      | 4 => orderedInterval (5096113584 / 1000000000000) (5096113631 / 1000000000000)
      | 5 => orderedInterval (-1664059070 / 1000000000000) (-1664058378 / 1000000000000)
      | 6 => orderedInterval (7876840568 / 1000000000000) (7876840605 / 1000000000000)
      | 7 => orderedInterval (-4909752871 / 1000000000000) (-4909751177 / 1000000000000)
      | _ => orderedInterval (-6065608447 / 1000000000000) (-6065608321 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-661300662 / 1000000000000) (-661300512 / 1000000000000)
      | 1 => orderedInterval (7888689425 / 1000000000000) (7888689456 / 1000000000000)
      | 2 => orderedInterval (1791235332 / 1000000000000) (1791235904 / 1000000000000)
      | 3 => orderedInterval (-69958648061 / 1000000000000) (-69958623962 / 1000000000000)
      | 4 => orderedInterval (-7996562580 / 1000000000000) (-7996562496 / 1000000000000)
      | 5 => orderedInterval (-7387859910 / 1000000000000) (-7387859018 / 1000000000000)
      | 6 => orderedInterval (-8561869815 / 1000000000000) (-8561869779 / 1000000000000)
      | 7 => orderedInterval (1701233936 / 1000000000000) (1701235200 / 1000000000000)
      | _ => orderedInterval (11128201240 / 1000000000000) (11128201451 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-25912629676 / 1000000000000) (-25912629499 / 1000000000000)
      | 1 => orderedInterval (7161287519 / 1000000000000) (7161287564 / 1000000000000)
      | 2 => orderedInterval (-5532459250 / 1000000000000) (-5532458168 / 1000000000000)
      | 3 => orderedInterval (10413163445 / 1000000000000) (10413217213 / 1000000000000)
      | 4 => orderedInterval (-15381178589 / 1000000000000) (-15381178434 / 1000000000000)
      | 5 => orderedInterval (666745192 / 1000000000000) (666746338 / 1000000000000)
      | 6 => orderedInterval (-8747039590 / 1000000000000) (-8747039555 / 1000000000000)
      | 7 => orderedInterval (5834524559 / 1000000000000) (5834525536 / 1000000000000)
      | _ => orderedInterval (-3633746328 / 1000000000000) (-3633745966 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1171083076 / 1000000000000) (-1171082864 / 1000000000000)
      | 1 => orderedInterval (-19317081486 / 1000000000000) (-19317081417 / 1000000000000)
      | 2 => orderedInterval (-9131690584 / 1000000000000) (-9131688507 / 1000000000000)
      | 3 => orderedInterval (334252006191 / 1000000000000) (334252126617 / 1000000000000)
      | 4 => orderedInterval (15245421890 / 1000000000000) (15245422181 / 1000000000000)
      | 5 => orderedInterval (18948532755 / 1000000000000) (18948534238 / 1000000000000)
      | 6 => orderedInterval (8650032238 / 1000000000000) (8650032272 / 1000000000000)
      | 7 => orderedInterval (-2331826699 / 1000000000000) (-2331825922 / 1000000000000)
      | _ => orderedInterval (-26498001519 / 1000000000000) (-26498000880 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21815229030 / 1000000000000) (21815237408 / 1000000000000)
    | 1 => orderedInterval (19136218027 / 1000000000000) (19136231863 / 1000000000000)
    | 2 => orderedInterval (-72056881095 / 1000000000000) (-72056853756 / 1000000000000)
    | 3 => orderedInterval (-35131332718 / 1000000000000) (-35131274971 / 1000000000000)
    | _ => orderedInterval (318646309710 / 1000000000000) (318646435718 / 1000000000000)

theorem compactCertificate282_stateChecks0 :
    compactCertificate282.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (313 / 2)) (orderedInterval (12981357295 / 1000000000000) (12981357296 / 1000000000000), orderedInterval (62403393103 / 1000000000000) (62403393104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (461108766693013 / 4000000000000)) (orderedInterval (13115790472 / 1000000000000) (13115790558 / 1000000000000), orderedInterval (-73204256045 / 1000000000000) (-73204255959 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (149113101071029 / 800000000000)) (orderedInterval (-56605910294 / 1000000000000) (-56605908694 / 1000000000000), orderedInterval (14686643939 / 1000000000000) (14686645538 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks1 :
    compactCertificate282.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (134550388099391 / 4000000000000)) (orderedInterval (18956063126 / 1000000000000) (18956063211 / 1000000000000), orderedInterval (-136548049503 / 1000000000000) (-136548049418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (361421268512627 / 4000000000000)) (orderedInterval (-2781623603 / 1000000000000) (-2781623598 / 1000000000000), orderedInterval (-83878033459 / 1000000000000) (-83878033455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (981329050461159 / 4000000000000)) (orderedInterval (44756267406 / 1000000000000) (44756267407 / 1000000000000), orderedInterval (24235775377 / 1000000000000) (24235775378 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks2 :
    compactCertificate282.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (722842537025567 / 4000000000000)) (orderedInterval (-39004337005 / 1000000000000) (-39004309203 / 1000000000000), orderedInterval (44846398761 / 1000000000000) (44846426562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1238603007649691 / 4000000000000)) (orderedInterval (24921686330 / 1000000000000) (24921690128 / 1000000000000), orderedInterval (-37919510835 / 1000000000000) (-37919507037 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (912349369455569 / 4000000000000)) (orderedInterval (23646761674 / 1000000000000) (23646763297 / 1000000000000), orderedInterval (-47295434014 / 1000000000000) (-47295432391 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks3 :
    compactCertificate282.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1399778553914687 / 4000000000000)) (orderedInterval (-38551338928 / 1000000000000) (-38551312314 / 1000000000000), orderedInterval (18303231766 / 1000000000000) (18303258379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (808162524908423 / 4000000000000)) (orderedInterval (55094411543 / 1000000000000) (55094412424 / 1000000000000), orderedInterval (-10885579806 / 1000000000000) (-10885578924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1434098582347507 / 4000000000000)) (orderedInterval (38768393907 / 1000000000000) (38768393908 / 1000000000000), orderedInterval (16458829631 / 1000000000000) (16458829632 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks4 :
    compactCertificate282.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1339920922004383 / 4000000000000)) (orderedInterval (16378657844 / 1000000000000) (16378658165 / 1000000000000), orderedInterval (-40425075564 / 1000000000000) (-40425075242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (956230795013839 / 4000000000000)) (orderedInterval (45550276960 / 1000000000000) (45550276961 / 1000000000000), orderedInterval (24157712643 / 1000000000000) (24157712644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1084263805537881 / 4000000000000)) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks5 :
    compactCertificate282.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (903946120873289 / 4000000000000)) (orderedInterval (28940444558 / 1000000000000) (28940444559 / 1000000000000), orderedInterval (44427799799 / 1000000000000) (44427799800 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (798663811727069 / 4000000000000)) (orderedInterval (-32403300499 / 1000000000000) (-32403291334 / 1000000000000), orderedInterval (46324560695 / 1000000000000) (46324569860 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (231483902055831 / 800000000000)) (orderedInterval (42082255054 / 1000000000000) (42082255055 / 1000000000000), orderedInterval (20644829346 / 1000000000000) (20644829347 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks6 :
    compactCertificate282.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (640296655416757 / 4000000000000)) (orderedInterval (-37537514965 / 1000000000000) (-37537514964 / 1000000000000), orderedInterval (-50557900007 / 1000000000000) (-50557900006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (542786565888077 / 4000000000000)) (orderedInterval (-67410049313 / 1000000000000) (-67410049310 / 1000000000000), orderedInterval (-11890311862 / 1000000000000) (-11890311859 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (339650630544431 / 4000000000000)) (orderedInterval (-66380130159 / 1000000000000) (-66380130158 / 1000000000000), orderedInterval (-55205937725 / 1000000000000) (-55205937724 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks7 :
    compactCertificate282.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (182665238733777 / 4000000000000)) (orderedInterval (73772318823 / 1000000000000) (73772353551 / 1000000000000), orderedInterval (-92995032605 / 1000000000000) (-92994997876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (495971656612331 / 4000000000000)) (orderedInterval (-55517631521 / 1000000000000) (-55517548634 / 1000000000000), orderedInterval (45524074203 / 1000000000000) (45524157090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (677206895182987 / 4000000000000)) (orderedInterval (26140085683 / 1000000000000) (26140085684 / 1000000000000), orderedInterval (55393278473 / 1000000000000) (55393278474 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_stateChecks8 :
    compactCertificate282.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (286349369455569 / 4000000000000)) (orderedInterval (-10761112784 / 1000000000000) (-10761112782 / 1000000000000), orderedInterval (-93612191949 / 1000000000000) (-93612191947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1163994289195249 / 4000000000000)) (orderedInterval (17547603273 / 1000000000000) (17547603697 / 1000000000000), orderedInterval (-43386712891 / 1000000000000) (-43386712467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (777494240956991 / 4000000000000)) (orderedInterval (21204819112 / 1000000000000) (21204819113 / 1000000000000), orderedInterval (53101845982 / 1000000000000) (53101845983 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_states : ∀ j,
    BesselStateValid (compactCertificate282.point j) (compactCertificate282.state j) :=
  compactCertificate282.statesValid_of_checks3 compactCertificate282_stateChecks0
    compactCertificate282_stateChecks1 compactCertificate282_stateChecks2
    compactCertificate282_stateChecks3 compactCertificate282_stateChecks4
    compactCertificate282_stateChecks5 compactCertificate282_stateChecks6
    compactCertificate282_stateChecks7 compactCertificate282_stateChecks8

theorem compactCertificate282_chunkChecks0_0 :
    compactCertificate282.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (313 / 2) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12981357295 / 1000000000000) (12981357296 / 1000000000000), orderedInterval (62403393103 / 1000000000000) (62403393104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (461108766693013 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13115790472 / 1000000000000) (13115790558 / 1000000000000), orderedInterval (-73204256045 / 1000000000000) (-73204255959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (149113101071029 / 800000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56605910294 / 1000000000000) (-56605908694 / 1000000000000), orderedInterval (14686643939 / 1000000000000) (14686645538 / 1000000000000)))) (orderedInterval (1945869963 / 1000000000000) (1945870070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (134550388099391 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (18956063126 / 1000000000000) (18956063211 / 1000000000000), orderedInterval (-136548049503 / 1000000000000) (-136548049418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (361421268512627 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2781623603 / 1000000000000) (-2781623598 / 1000000000000), orderedInterval (-83878033459 / 1000000000000) (-83878033455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (981329050461159 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (44756267406 / 1000000000000) (44756267407 / 1000000000000), orderedInterval (24235775377 / 1000000000000) (24235775378 / 1000000000000)))) (orderedInterval (-3488928773 / 1000000000000) (-3488928752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (722842537025567 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39004337005 / 1000000000000) (-39004309203 / 1000000000000), orderedInterval (44846398761 / 1000000000000) (44846426562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1238603007649691 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24921686330 / 1000000000000) (24921690128 / 1000000000000), orderedInterval (-37919510835 / 1000000000000) (-37919507037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (912349369455569 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23646761674 / 1000000000000) (23646763297 / 1000000000000), orderedInterval (-47295434014 / 1000000000000) (-47295432391 / 1000000000000)))) (orderedInterval (-197189065 / 1000000000000) (-197188899 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks0_1 :
    compactCertificate282.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1399778553914687 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38551338928 / 1000000000000) (-38551312314 / 1000000000000), orderedInterval (18303231766 / 1000000000000) (18303258379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (808162524908423 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55094411543 / 1000000000000) (55094412424 / 1000000000000), orderedInterval (-10885579806 / 1000000000000) (-10885578924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1434098582347507 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38768393907 / 1000000000000) (38768393908 / 1000000000000), orderedInterval (16458829631 / 1000000000000) (16458829632 / 1000000000000)))) (orderedInterval (16443300839 / 1000000000000) (16443305696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1339920922004383 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16378657844 / 1000000000000) (16378658165 / 1000000000000), orderedInterval (-40425075564 / 1000000000000) (-40425075242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (956230795013839 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (45550276960 / 1000000000000) (45550276961 / 1000000000000), orderedInterval (24157712643 / 1000000000000) (24157712644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000)))) (orderedInterval (3767736157 / 1000000000000) (3767736185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (903946120873289 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28940444558 / 1000000000000) (28940444559 / 1000000000000), orderedInterval (44427799799 / 1000000000000) (44427799800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (798663811727069 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32403300499 / 1000000000000) (-32403291334 / 1000000000000), orderedInterval (46324560695 / 1000000000000) (46324569860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (231483902055831 / 800000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42082255054 / 1000000000000) (42082255055 / 1000000000000), orderedInterval (20644829346 / 1000000000000) (20644829347 / 1000000000000)))) (orderedInterval (3265999337 / 1000000000000) (3265999877 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks0_2 :
    compactCertificate282.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (640296655416757 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37537514965 / 1000000000000) (-37537514964 / 1000000000000), orderedInterval (-50557900007 / 1000000000000) (-50557900006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (542786565888077 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67410049313 / 1000000000000) (-67410049310 / 1000000000000), orderedInterval (-11890311862 / 1000000000000) (-11890311859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (339650630544431 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-66380130159 / 1000000000000) (-66380130158 / 1000000000000), orderedInterval (-55205937725 / 1000000000000) (-55205937724 / 1000000000000)))) (orderedInterval (7656347613 / 1000000000000) (7656347653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (182665238733777 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73772318823 / 1000000000000) (73772353551 / 1000000000000), orderedInterval (-92995032605 / 1000000000000) (-92994997876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (495971656612331 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55517631521 / 1000000000000) (-55517548634 / 1000000000000), orderedInterval (45524074203 / 1000000000000) (45524157090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (677206895182987 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26140085683 / 1000000000000) (26140085684 / 1000000000000), orderedInterval (55393278473 / 1000000000000) (55393278474 / 1000000000000)))) (orderedInterval (-2106042813 / 1000000000000) (-2106040272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (286349369455569 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10761112784 / 1000000000000) (-10761112782 / 1000000000000), orderedInterval (-93612191949 / 1000000000000) (-93612191947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1163994289195249 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17547603273 / 1000000000000) (17547603697 / 1000000000000), orderedInterval (-43386712891 / 1000000000000) (-43386712467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (777494240956991 / 4000000000000) 0 (IntervalRat.scale (313 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21204819112 / 1000000000000) (21204819113 / 1000000000000), orderedInterval (53101845982 / 1000000000000) (53101845983 / 1000000000000)))) (orderedInterval (-5471864228 / 1000000000000) (-5471864150 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks0 :
    compactCertificate282.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate282.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate282_chunkChecks0_0
    compactCertificate282_chunkChecks0_1 compactCertificate282_chunkChecks0_2

theorem compactCertificate282_chunkChecks1_0 :
    compactCertificate282.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (313 / 2) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12981357295 / 1000000000000) (12981357296 / 1000000000000), orderedInterval (62403393103 / 1000000000000) (62403393104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (461108766693013 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13115790472 / 1000000000000) (13115790558 / 1000000000000), orderedInterval (-73204256045 / 1000000000000) (-73204255959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (149113101071029 / 800000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56605910294 / 1000000000000) (-56605908694 / 1000000000000), orderedInterval (14686643939 / 1000000000000) (14686645538 / 1000000000000)))) (orderedInterval (25258510413 / 1000000000000) (25258510538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (134550388099391 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (18956063126 / 1000000000000) (18956063211 / 1000000000000), orderedInterval (-136548049503 / 1000000000000) (-136548049418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (361421268512627 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2781623603 / 1000000000000) (-2781623598 / 1000000000000), orderedInterval (-83878033459 / 1000000000000) (-83878033455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (981329050461159 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (44756267406 / 1000000000000) (44756267407 / 1000000000000), orderedInterval (24235775377 / 1000000000000) (24235775378 / 1000000000000)))) (orderedInterval (-4150605880 / 1000000000000) (-4150605858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (722842537025567 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39004337005 / 1000000000000) (-39004309203 / 1000000000000), orderedInterval (44846398761 / 1000000000000) (44846426562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1238603007649691 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24921686330 / 1000000000000) (24921690128 / 1000000000000), orderedInterval (-37919510835 / 1000000000000) (-37919507037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (912349369455569 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23646761674 / 1000000000000) (23646763297 / 1000000000000), orderedInterval (-47295434014 / 1000000000000) (-47295432391 / 1000000000000)))) (orderedInterval (648254715 / 1000000000000) (648255020 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks1_1 :
    compactCertificate282.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1399778553914687 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38551338928 / 1000000000000) (-38551312314 / 1000000000000), orderedInterval (18303231766 / 1000000000000) (18303258379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (808162524908423 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55094411543 / 1000000000000) (55094412424 / 1000000000000), orderedInterval (-10885579806 / 1000000000000) (-10885578924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1434098582347507 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38768393907 / 1000000000000) (38768393908 / 1000000000000), orderedInterval (16458829631 / 1000000000000) (16458829632 / 1000000000000)))) (orderedInterval (-2953474985 / 1000000000000) (-2953464197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1339920922004383 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16378657844 / 1000000000000) (16378658165 / 1000000000000), orderedInterval (-40425075564 / 1000000000000) (-40425075242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (956230795013839 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (45550276960 / 1000000000000) (45550276961 / 1000000000000), orderedInterval (24157712643 / 1000000000000) (24157712644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000)))) (orderedInterval (5096113584 / 1000000000000) (5096113631 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (903946120873289 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28940444558 / 1000000000000) (28940444559 / 1000000000000), orderedInterval (44427799799 / 1000000000000) (44427799800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (798663811727069 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32403300499 / 1000000000000) (-32403291334 / 1000000000000), orderedInterval (46324560695 / 1000000000000) (46324569860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (231483902055831 / 800000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42082255054 / 1000000000000) (42082255055 / 1000000000000), orderedInterval (20644829346 / 1000000000000) (20644829347 / 1000000000000)))) (orderedInterval (-1664059070 / 1000000000000) (-1664058378 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks1_2 :
    compactCertificate282.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (640296655416757 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37537514965 / 1000000000000) (-37537514964 / 1000000000000), orderedInterval (-50557900007 / 1000000000000) (-50557900006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (542786565888077 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67410049313 / 1000000000000) (-67410049310 / 1000000000000), orderedInterval (-11890311862 / 1000000000000) (-11890311859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (339650630544431 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-66380130159 / 1000000000000) (-66380130158 / 1000000000000), orderedInterval (-55205937725 / 1000000000000) (-55205937724 / 1000000000000)))) (orderedInterval (7876840568 / 1000000000000) (7876840605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (182665238733777 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73772318823 / 1000000000000) (73772353551 / 1000000000000), orderedInterval (-92995032605 / 1000000000000) (-92994997876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (495971656612331 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55517631521 / 1000000000000) (-55517548634 / 1000000000000), orderedInterval (45524074203 / 1000000000000) (45524157090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (677206895182987 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26140085683 / 1000000000000) (26140085684 / 1000000000000), orderedInterval (55393278473 / 1000000000000) (55393278474 / 1000000000000)))) (orderedInterval (-4909752871 / 1000000000000) (-4909751177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (286349369455569 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10761112784 / 1000000000000) (-10761112782 / 1000000000000), orderedInterval (-93612191949 / 1000000000000) (-93612191947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1163994289195249 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17547603273 / 1000000000000) (17547603697 / 1000000000000), orderedInterval (-43386712891 / 1000000000000) (-43386712467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (777494240956991 / 4000000000000) 1 (IntervalRat.scale (313 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21204819112 / 1000000000000) (21204819113 / 1000000000000), orderedInterval (53101845982 / 1000000000000) (53101845983 / 1000000000000)))) (orderedInterval (-6065608447 / 1000000000000) (-6065608321 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks1 :
    compactCertificate282.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate282.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate282_chunkChecks1_0
    compactCertificate282_chunkChecks1_1 compactCertificate282_chunkChecks1_2

theorem compactCertificate282_chunkChecks2_0 :
    compactCertificate282.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (313 / 2) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12981357295 / 1000000000000) (12981357296 / 1000000000000), orderedInterval (62403393103 / 1000000000000) (62403393104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (461108766693013 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13115790472 / 1000000000000) (13115790558 / 1000000000000), orderedInterval (-73204256045 / 1000000000000) (-73204255959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (149113101071029 / 800000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56605910294 / 1000000000000) (-56605908694 / 1000000000000), orderedInterval (14686643939 / 1000000000000) (14686645538 / 1000000000000)))) (orderedInterval (-661300662 / 1000000000000) (-661300512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (134550388099391 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (18956063126 / 1000000000000) (18956063211 / 1000000000000), orderedInterval (-136548049503 / 1000000000000) (-136548049418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (361421268512627 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2781623603 / 1000000000000) (-2781623598 / 1000000000000), orderedInterval (-83878033459 / 1000000000000) (-83878033455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (981329050461159 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (44756267406 / 1000000000000) (44756267407 / 1000000000000), orderedInterval (24235775377 / 1000000000000) (24235775378 / 1000000000000)))) (orderedInterval (7888689425 / 1000000000000) (7888689456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (722842537025567 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39004337005 / 1000000000000) (-39004309203 / 1000000000000), orderedInterval (44846398761 / 1000000000000) (44846426562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1238603007649691 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24921686330 / 1000000000000) (24921690128 / 1000000000000), orderedInterval (-37919510835 / 1000000000000) (-37919507037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (912349369455569 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23646761674 / 1000000000000) (23646763297 / 1000000000000), orderedInterval (-47295434014 / 1000000000000) (-47295432391 / 1000000000000)))) (orderedInterval (1791235332 / 1000000000000) (1791235904 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks2_1 :
    compactCertificate282.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1399778553914687 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38551338928 / 1000000000000) (-38551312314 / 1000000000000), orderedInterval (18303231766 / 1000000000000) (18303258379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (808162524908423 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55094411543 / 1000000000000) (55094412424 / 1000000000000), orderedInterval (-10885579806 / 1000000000000) (-10885578924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1434098582347507 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38768393907 / 1000000000000) (38768393908 / 1000000000000), orderedInterval (16458829631 / 1000000000000) (16458829632 / 1000000000000)))) (orderedInterval (-69958648061 / 1000000000000) (-69958623962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1339920922004383 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16378657844 / 1000000000000) (16378658165 / 1000000000000), orderedInterval (-40425075564 / 1000000000000) (-40425075242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (956230795013839 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (45550276960 / 1000000000000) (45550276961 / 1000000000000), orderedInterval (24157712643 / 1000000000000) (24157712644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000)))) (orderedInterval (-7996562580 / 1000000000000) (-7996562496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (903946120873289 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28940444558 / 1000000000000) (28940444559 / 1000000000000), orderedInterval (44427799799 / 1000000000000) (44427799800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (798663811727069 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32403300499 / 1000000000000) (-32403291334 / 1000000000000), orderedInterval (46324560695 / 1000000000000) (46324569860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (231483902055831 / 800000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42082255054 / 1000000000000) (42082255055 / 1000000000000), orderedInterval (20644829346 / 1000000000000) (20644829347 / 1000000000000)))) (orderedInterval (-7387859910 / 1000000000000) (-7387859018 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks2_2 :
    compactCertificate282.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (640296655416757 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37537514965 / 1000000000000) (-37537514964 / 1000000000000), orderedInterval (-50557900007 / 1000000000000) (-50557900006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (542786565888077 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67410049313 / 1000000000000) (-67410049310 / 1000000000000), orderedInterval (-11890311862 / 1000000000000) (-11890311859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (339650630544431 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-66380130159 / 1000000000000) (-66380130158 / 1000000000000), orderedInterval (-55205937725 / 1000000000000) (-55205937724 / 1000000000000)))) (orderedInterval (-8561869815 / 1000000000000) (-8561869779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (182665238733777 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73772318823 / 1000000000000) (73772353551 / 1000000000000), orderedInterval (-92995032605 / 1000000000000) (-92994997876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (495971656612331 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55517631521 / 1000000000000) (-55517548634 / 1000000000000), orderedInterval (45524074203 / 1000000000000) (45524157090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (677206895182987 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26140085683 / 1000000000000) (26140085684 / 1000000000000), orderedInterval (55393278473 / 1000000000000) (55393278474 / 1000000000000)))) (orderedInterval (1701233936 / 1000000000000) (1701235200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (286349369455569 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10761112784 / 1000000000000) (-10761112782 / 1000000000000), orderedInterval (-93612191949 / 1000000000000) (-93612191947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1163994289195249 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17547603273 / 1000000000000) (17547603697 / 1000000000000), orderedInterval (-43386712891 / 1000000000000) (-43386712467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (777494240956991 / 4000000000000) 2 (IntervalRat.scale (313 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21204819112 / 1000000000000) (21204819113 / 1000000000000), orderedInterval (53101845982 / 1000000000000) (53101845983 / 1000000000000)))) (orderedInterval (11128201240 / 1000000000000) (11128201451 / 1000000000000))) = true
  rfl'

theorem compactCertificate282_chunkChecks2 :
    compactCertificate282.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate282.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate282_chunkChecks2_0
    compactCertificate282_chunkChecks2_1 compactCertificate282_chunkChecks2_2

theorem compactCertificate282_chunkChecks3_0 :
    compactCertificate282.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (313 / 2) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12981357295 / 1000000000000) (12981357296 / 1000000000000), orderedInterval (62403393103 / 1000000000000) (62403393104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (461108766693013 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13115790472 / 1000000000000) (13115790558 / 1000000000000), orderedInterval (-73204256045 / 1000000000000) (-73204255959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (149113101071029 / 800000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56605910294 / 1000000000000) (-56605908694 / 1000000000000), orderedInterval (14686643939 / 1000000000000) (14686645538 / 1000000000000)))) (orderedInterval (-25912629676 / 1000000000000) (-25912629499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (134550388099391 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (18956063126 / 1000000000000) (18956063211 / 1000000000000), orderedInterval (-136548049503 / 1000000000000) (-136548049418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (361421268512627 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2781623603 / 1000000000000) (-2781623598 / 1000000000000), orderedInterval (-83878033459 / 1000000000000) (-83878033455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (981329050461159 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (44756267406 / 1000000000000) (44756267407 / 1000000000000), orderedInterval (24235775377 / 1000000000000) (24235775378 / 1000000000000)))) (orderedInterval (7161287519 / 1000000000000) (7161287564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (722842537025567 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39004337005 / 1000000000000) (-39004309203 / 1000000000000), orderedInterval (44846398761 / 1000000000000) (44846426562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1238603007649691 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24921686330 / 1000000000000) (24921690128 / 1000000000000), orderedInterval (-37919510835 / 1000000000000) (-37919507037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (912349369455569 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23646761674 / 1000000000000) (23646763297 / 1000000000000), orderedInterval (-47295434014 / 1000000000000) (-47295432391 / 1000000000000)))) (orderedInterval (-5532459250 / 1000000000000) (-5532458168 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate282_chunkChecks3_1 :
    compactCertificate282.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1399778553914687 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38551338928 / 1000000000000) (-38551312314 / 1000000000000), orderedInterval (18303231766 / 1000000000000) (18303258379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (808162524908423 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55094411543 / 1000000000000) (55094412424 / 1000000000000), orderedInterval (-10885579806 / 1000000000000) (-10885578924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1434098582347507 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38768393907 / 1000000000000) (38768393908 / 1000000000000), orderedInterval (16458829631 / 1000000000000) (16458829632 / 1000000000000)))) (orderedInterval (10413163445 / 1000000000000) (10413217213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1339920922004383 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16378657844 / 1000000000000) (16378658165 / 1000000000000), orderedInterval (-40425075564 / 1000000000000) (-40425075242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (956230795013839 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (45550276960 / 1000000000000) (45550276961 / 1000000000000), orderedInterval (24157712643 / 1000000000000) (24157712644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000)))) (orderedInterval (-15381178589 / 1000000000000) (-15381178434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (903946120873289 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28940444558 / 1000000000000) (28940444559 / 1000000000000), orderedInterval (44427799799 / 1000000000000) (44427799800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (798663811727069 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32403300499 / 1000000000000) (-32403291334 / 1000000000000), orderedInterval (46324560695 / 1000000000000) (46324569860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (231483902055831 / 800000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42082255054 / 1000000000000) (42082255055 / 1000000000000), orderedInterval (20644829346 / 1000000000000) (20644829347 / 1000000000000)))) (orderedInterval (666745192 / 1000000000000) (666746338 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate282_chunkChecks3_2 :
    compactCertificate282.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (640296655416757 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37537514965 / 1000000000000) (-37537514964 / 1000000000000), orderedInterval (-50557900007 / 1000000000000) (-50557900006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (542786565888077 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67410049313 / 1000000000000) (-67410049310 / 1000000000000), orderedInterval (-11890311862 / 1000000000000) (-11890311859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (339650630544431 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-66380130159 / 1000000000000) (-66380130158 / 1000000000000), orderedInterval (-55205937725 / 1000000000000) (-55205937724 / 1000000000000)))) (orderedInterval (-8747039590 / 1000000000000) (-8747039555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (182665238733777 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73772318823 / 1000000000000) (73772353551 / 1000000000000), orderedInterval (-92995032605 / 1000000000000) (-92994997876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (495971656612331 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55517631521 / 1000000000000) (-55517548634 / 1000000000000), orderedInterval (45524074203 / 1000000000000) (45524157090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (677206895182987 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26140085683 / 1000000000000) (26140085684 / 1000000000000), orderedInterval (55393278473 / 1000000000000) (55393278474 / 1000000000000)))) (orderedInterval (5834524559 / 1000000000000) (5834525536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (286349369455569 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10761112784 / 1000000000000) (-10761112782 / 1000000000000), orderedInterval (-93612191949 / 1000000000000) (-93612191947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1163994289195249 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17547603273 / 1000000000000) (17547603697 / 1000000000000), orderedInterval (-43386712891 / 1000000000000) (-43386712467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (777494240956991 / 4000000000000) 3 (IntervalRat.scale (313 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21204819112 / 1000000000000) (21204819113 / 1000000000000), orderedInterval (53101845982 / 1000000000000) (53101845983 / 1000000000000)))) (orderedInterval (-3633746328 / 1000000000000) (-3633745966 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate282_chunkChecks3 :
    compactCertificate282.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate282.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate282_chunkChecks3_0
    compactCertificate282_chunkChecks3_1 compactCertificate282_chunkChecks3_2

theorem compactCertificate282_chunkChecks4_0 :
    compactCertificate282.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (313 / 2) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12981357295 / 1000000000000) (12981357296 / 1000000000000), orderedInterval (62403393103 / 1000000000000) (62403393104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (461108766693013 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13115790472 / 1000000000000) (13115790558 / 1000000000000), orderedInterval (-73204256045 / 1000000000000) (-73204255959 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (149113101071029 / 800000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56605910294 / 1000000000000) (-56605908694 / 1000000000000), orderedInterval (14686643939 / 1000000000000) (14686645538 / 1000000000000)))) (orderedInterval (-1171083076 / 1000000000000) (-1171082864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (134550388099391 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (18956063126 / 1000000000000) (18956063211 / 1000000000000), orderedInterval (-136548049503 / 1000000000000) (-136548049418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (361421268512627 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-2781623603 / 1000000000000) (-2781623598 / 1000000000000), orderedInterval (-83878033459 / 1000000000000) (-83878033455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (981329050461159 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (44756267406 / 1000000000000) (44756267407 / 1000000000000), orderedInterval (24235775377 / 1000000000000) (24235775378 / 1000000000000)))) (orderedInterval (-19317081486 / 1000000000000) (-19317081417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (722842537025567 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39004337005 / 1000000000000) (-39004309203 / 1000000000000), orderedInterval (44846398761 / 1000000000000) (44846426562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1238603007649691 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24921686330 / 1000000000000) (24921690128 / 1000000000000), orderedInterval (-37919510835 / 1000000000000) (-37919507037 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (912349369455569 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23646761674 / 1000000000000) (23646763297 / 1000000000000), orderedInterval (-47295434014 / 1000000000000) (-47295432391 / 1000000000000)))) (orderedInterval (-9131690584 / 1000000000000) (-9131688507 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate282_chunkChecks4_1 :
    compactCertificate282.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1399778553914687 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38551338928 / 1000000000000) (-38551312314 / 1000000000000), orderedInterval (18303231766 / 1000000000000) (18303258379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (808162524908423 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (55094411543 / 1000000000000) (55094412424 / 1000000000000), orderedInterval (-10885579806 / 1000000000000) (-10885578924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1434098582347507 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38768393907 / 1000000000000) (38768393908 / 1000000000000), orderedInterval (16458829631 / 1000000000000) (16458829632 / 1000000000000)))) (orderedInterval (334252006191 / 1000000000000) (334252126617 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1339920922004383 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16378657844 / 1000000000000) (16378658165 / 1000000000000), orderedInterval (-40425075564 / 1000000000000) (-40425075242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (956230795013839 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (45550276960 / 1000000000000) (45550276961 / 1000000000000), orderedInterval (24157712643 / 1000000000000) (24157712644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1084263805537881 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48204639707 / 1000000000000) (48204640156 / 1000000000000), orderedInterval (-5077671270 / 1000000000000) (-5077670821 / 1000000000000)))) (orderedInterval (15245421890 / 1000000000000) (15245422181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (903946120873289 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28940444558 / 1000000000000) (28940444559 / 1000000000000), orderedInterval (44427799799 / 1000000000000) (44427799800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (798663811727069 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32403300499 / 1000000000000) (-32403291334 / 1000000000000), orderedInterval (46324560695 / 1000000000000) (46324569860 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (231483902055831 / 800000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42082255054 / 1000000000000) (42082255055 / 1000000000000), orderedInterval (20644829346 / 1000000000000) (20644829347 / 1000000000000)))) (orderedInterval (18948532755 / 1000000000000) (18948534238 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate282_chunkChecks4_2 :
    compactCertificate282.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (640296655416757 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-37537514965 / 1000000000000) (-37537514964 / 1000000000000), orderedInterval (-50557900007 / 1000000000000) (-50557900006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (542786565888077 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-67410049313 / 1000000000000) (-67410049310 / 1000000000000), orderedInterval (-11890311862 / 1000000000000) (-11890311859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (339650630544431 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-66380130159 / 1000000000000) (-66380130158 / 1000000000000), orderedInterval (-55205937725 / 1000000000000) (-55205937724 / 1000000000000)))) (orderedInterval (8650032238 / 1000000000000) (8650032272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (182665238733777 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (73772318823 / 1000000000000) (73772353551 / 1000000000000), orderedInterval (-92995032605 / 1000000000000) (-92994997876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (495971656612331 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55517631521 / 1000000000000) (-55517548634 / 1000000000000), orderedInterval (45524074203 / 1000000000000) (45524157090 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (677206895182987 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (26140085683 / 1000000000000) (26140085684 / 1000000000000), orderedInterval (55393278473 / 1000000000000) (55393278474 / 1000000000000)))) (orderedInterval (-2331826699 / 1000000000000) (-2331825922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (286349369455569 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-10761112784 / 1000000000000) (-10761112782 / 1000000000000), orderedInterval (-93612191949 / 1000000000000) (-93612191947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1163994289195249 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17547603273 / 1000000000000) (17547603697 / 1000000000000), orderedInterval (-43386712891 / 1000000000000) (-43386712467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (777494240956991 / 4000000000000) 4 (IntervalRat.scale (313 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (21204819112 / 1000000000000) (21204819113 / 1000000000000), orderedInterval (53101845982 / 1000000000000) (53101845983 / 1000000000000)))) (orderedInterval (-26498001519 / 1000000000000) (-26498000880 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate282_chunkChecks4 :
    compactCertificate282.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate282.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate282_chunkChecks4_0
    compactCertificate282_chunkChecks4_1 compactCertificate282_chunkChecks4_2

theorem compactCertificate282_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate282.chunkCheck r b = true :=
  compactCertificate282.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate282_chunkChecks0
    · exact compactCertificate282_chunkChecks1
    · exact compactCertificate282_chunkChecks2
    · exact compactCertificate282_chunkChecks3
    · exact compactCertificate282_chunkChecks4)

theorem compactCertificate282_coefficient0 :
    compactCertificate282.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate282_coefficient1 :
    compactCertificate282.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate282_coefficient2 :
    compactCertificate282.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate282_coefficient3 :
    compactCertificate282.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate282_coefficient4 :
    compactCertificate282.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate282_coefficients : ∀ r : Fin 5,
    compactCertificate282.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate282_coefficient0
  · exact compactCertificate282_coefficient1
  · exact compactCertificate282_coefficient2
  · exact compactCertificate282_coefficient3
  · exact compactCertificate282_coefficient4

theorem compactCertificate282_lower : (1 : ℚ) ≤ compactCertificate282.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate282, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate282_proves {t : ℝ} (ht : t ∈ compactCertificate282.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate282.proves compactCertificate282_states compactCertificate282_chunks
    compactCertificate282_coefficients compactCertificate282_lower ht

end Erdos232
