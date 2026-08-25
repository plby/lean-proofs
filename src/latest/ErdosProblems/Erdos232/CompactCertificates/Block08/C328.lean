/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate328 : CompactCertificate where
  left := 200
  right := 201
  center := 401 / 2
  grid := fun i =>
    match i.val with
    | 0 => 64
    | 1 => 47
    | 2 => 76
    | 3 => 14
    | 4 => 37
    | 5 => 100
    | 6 => 74
    | 7 => 126
    | 8 => 93
    | 9 => 143
    | 10 => 82
    | 11 => 146
    | 12 => 137
    | 13 => 98
    | 14 => 111
    | 15 => 92
    | 16 => 81
    | 17 => 118
    | 18 => 65
    | 19 => 55
    | 20 => 35
    | 21 => 19
    | 22 => 51
    | 23 => 69
    | 24 => 29
    | 25 => 119
    | _ => 79
  point := fun i =>
    match i.val with
    | 0 => 401 / 2
    | 1 => 590749570108301 / 4000000000000
    | 2 => 191036273257133 / 800000000000
    | 3 => 172379251207207 / 4000000000000
    | 4 => 463034915889979 / 4000000000000
    | 5 => 1257229869760143 / 4000000000000
    | 6 => 926069831780359 / 4000000000000
    | 7 => 1586836441110307 / 4000000000000
    | 8 => 1168856540420713 / 4000000000000
    | 9 => 1793326517954599 / 4000000000000
    | 10 => 1035377547885871 / 4000000000000
    | 11 => 1837295627863739 / 4000000000000
    | 12 => 1716639903270791 / 4000000000000
    | 13 => 1225075235784503 / 4000000000000
    | 14 => 1389104747669937 / 4000000000000
    | 15 => 1158090717157153 / 4000000000000
    | 16 => 1023208269976213 / 4000000000000
    | 17 => 296565638097087 / 800000000000
    | 18 => 820316162370989 / 4000000000000
    | 19 => 695391095594629 / 4000000000000
    | 20 => 435143459579287 / 4000000000000
    | 21 => 234021599783529 / 4000000000000
    | 22 => 635414167097587 / 4000000000000
    | 23 => 867603721943699 / 4000000000000
    | 24 => 366856540420713 / 4000000000000
    | 25 => 1491251469544073 / 4000000000000
    | _ => 996086871002407 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (12453299390 / 1000000000000) (12453299391 / 1000000000000), orderedInterval (54924246437 / 1000000000000) (54924246438 / 1000000000000))
    | 1 => (orderedInterval (-47872739195 / 1000000000000) (-47872739194 / 1000000000000), orderedInterval (-44768864391 / 1000000000000) (-44768864390 / 1000000000000))
    | 2 => (orderedInterval (37722104447 / 1000000000000) (37722104448 / 1000000000000), orderedInterval (35177311965 / 1000000000000) (35177311966 / 1000000000000))
    | 3 => (orderedInterval (-12736381632 / 1000000000000) (-12736381582 / 1000000000000), orderedInterval (121024939499 / 1000000000000) (121024939549 / 1000000000000))
    | 4 => (orderedInterval (-22206987513 / 1000000000000) (-22206987512 / 1000000000000), orderedInterval (-70660226453 / 1000000000000) (-70660226452 / 1000000000000))
    | 5 => (orderedInterval (36163025611 / 1000000000000) (36163025612 / 1000000000000), orderedInterval (26732451635 / 1000000000000) (26732451636 / 1000000000000))
    | 6 => (orderedInterval (-9157806870 / 1000000000000) (-9157806834 / 1000000000000), orderedInterval (51652234980 / 1000000000000) (51652235015 / 1000000000000))
    | 7 => (orderedInterval (39922355036 / 1000000000000) (39922355802 / 1000000000000), orderedInterval (-3360357379 / 1000000000000) (-3360356612 / 1000000000000))
    | 8 => (orderedInterval (-34474455958 / 1000000000000) (-34474455957 / 1000000000000), orderedInterval (-31407162492 / 1000000000000) (-31407162491 / 1000000000000))
    | 9 => (orderedInterval (4922329895 / 1000000000000) (4922329899 / 1000000000000), orderedInterval (-37365182726 / 1000000000000) (-37365182723 / 1000000000000))
    | 10 => (orderedInterval (44700876215 / 1000000000000) (44700894452 / 1000000000000), orderedInterval (-21564182627 / 1000000000000) (-21564164390 / 1000000000000))
    | 11 => (orderedInterval (36893728287 / 1000000000000) (36893728352 / 1000000000000), orderedInterval (4944328387 / 1000000000000) (4944328453 / 1000000000000))
    | 12 => (orderedInterval (16860517558 / 1000000000000) (16860517975 / 1000000000000), orderedInterval (-34648137355 / 1000000000000) (-34648136938 / 1000000000000))
    | 13 => (orderedInterval (-33405263953 / 1000000000000) (-33405223292 / 1000000000000), orderedInterval (31082247933 / 1000000000000) (31082288594 / 1000000000000))
    | 14 => (orderedInterval (26100523614 / 1000000000000) (26100530354 / 1000000000000), orderedInterval (-33977868041 / 1000000000000) (-33977861301 / 1000000000000))
    | 15 => (orderedInterval (44938298302 / 1000000000000) (44938298304 / 1000000000000), orderedInterval (13316659095 / 1000000000000) (13316659097 / 1000000000000))
    | 16 => (orderedInterval (-42603409194 / 1000000000000) (-42603364388 / 1000000000000), orderedInterval (26038392412 / 1000000000000) (26038437218 / 1000000000000))
    | 17 => (orderedInterval (29266971563 / 1000000000000) (29266971564 / 1000000000000), orderedInterval (29299180570 / 1000000000000) (29299180571 / 1000000000000))
    | 18 => (orderedInterval (-55492800321 / 1000000000000) (-55492800076 / 1000000000000), orderedInterval (5115803086 / 1000000000000) (5115803331 / 1000000000000))
    | 19 => (orderedInterval (-58255437654 / 1000000000000) (-58255435726 / 1000000000000), orderedInterval (16545248682 / 1000000000000) (16545250610 / 1000000000000))
    | 20 => (orderedInterval (28774194466 / 1000000000000) (28774195776 / 1000000000000), orderedInterval (-71013382033 / 1000000000000) (-71013380723 / 1000000000000))
    | 21 => (orderedInterval (40774526378 / 1000000000000) (40774528460 / 1000000000000), orderedInterval (-96364580647 / 1000000000000) (-96364578565 / 1000000000000))
    | 22 => (orderedInterval (34855372785 / 1000000000000) (34855381276 / 1000000000000), orderedInterval (-52955713957 / 1000000000000) (-52955705466 / 1000000000000))
    | 23 => (orderedInterval (-42966423407 / 1000000000000) (-42966423406 / 1000000000000), orderedInterval (-32900289174 / 1000000000000) (-32900289173 / 1000000000000))
    | 24 => (orderedInterval (-81985737038 / 1000000000000) (-81985737036 / 1000000000000), orderedInterval (-14371646099 / 1000000000000) (-14371646097 / 1000000000000))
    | 25 => (orderedInterval (10287403606 / 1000000000000) (10287403644 / 1000000000000), orderedInterval (-40036075748 / 1000000000000) (-40036075710 / 1000000000000))
    | _ => (orderedInterval (-50498439928 / 1000000000000) (-50498439734 / 1000000000000), orderedInterval (2628324855 / 1000000000000) (2628325049 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (6703546954 / 1000000000000) (6703546969 / 1000000000000)
      | 1 => orderedInterval (-3243451698 / 1000000000000) (-3243451673 / 1000000000000)
      | 2 => orderedInterval (-2064544771 / 1000000000000) (-2064544735 / 1000000000000)
      | 3 => orderedInterval (7681989307 / 1000000000000) (7681990748 / 1000000000000)
      | 4 => orderedInterval (-3595365610 / 1000000000000) (-3595361698 / 1000000000000)
      | 5 => orderedInterval (3706331679 / 1000000000000) (3706334263 / 1000000000000)
      | 6 => orderedInterval (13106886090 / 1000000000000) (13106886331 / 1000000000000)
      | 7 => orderedInterval (1749232462 / 1000000000000) (1749232718 / 1000000000000)
      | _ => orderedInterval (8143196987 / 1000000000000) (8143197082 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (23921285029 / 1000000000000) (23921285046 / 1000000000000)
      | 1 => orderedInterval (-4750844084 / 1000000000000) (-4750844056 / 1000000000000)
      | 2 => orderedInterval (-901183274 / 1000000000000) (-901183207 / 1000000000000)
      | 3 => orderedInterval (14393549923 / 1000000000000) (14393551855 / 1000000000000)
      | 4 => orderedInterval (6126427534 / 1000000000000) (6126433522 / 1000000000000)
      | 5 => orderedInterval (-292030494 / 1000000000000) (-292027195 / 1000000000000)
      | 6 => orderedInterval (-2902989782 / 1000000000000) (-2902989577 / 1000000000000)
      | 7 => orderedInterval (4198767441 / 1000000000000) (4198767628 / 1000000000000)
      | _ => orderedInterval (5407734271 / 1000000000000) (5407734400 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-7953240064 / 1000000000000) (-7953240045 / 1000000000000)
      | 1 => orderedInterval (6605177458 / 1000000000000) (6605177497 / 1000000000000)
      | 2 => orderedInterval (6594861308 / 1000000000000) (6594861436 / 1000000000000)
      | 3 => orderedInterval (-28743506746 / 1000000000000) (-28743504079 / 1000000000000)
      | 4 => orderedInterval (9130990462 / 1000000000000) (9130999665 / 1000000000000)
      | 5 => orderedInterval (-7610693342 / 1000000000000) (-7610689109 / 1000000000000)
      | 6 => orderedInterval (-12022991589 / 1000000000000) (-12022991407 / 1000000000000)
      | 7 => orderedInterval (-3314111404 / 1000000000000) (-3314111257 / 1000000000000)
      | _ => orderedInterval (-11643905199 / 1000000000000) (-11643905016 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-25050416700 / 1000000000000) (-25050416678 / 1000000000000)
      | 1 => orderedInterval (7797410623 / 1000000000000) (7797410680 / 1000000000000)
      | 2 => orderedInterval (1514041878 / 1000000000000) (1514042126 / 1000000000000)
      | 3 => orderedInterval (-79099193787 / 1000000000000) (-79099189976 / 1000000000000)
      | 4 => orderedInterval (-17548963669 / 1000000000000) (-17548949559 / 1000000000000)
      | 5 => orderedInterval (-2072082690 / 1000000000000) (-2072077281 / 1000000000000)
      | 6 => orderedInterval (1914921948 / 1000000000000) (1914922113 / 1000000000000)
      | 7 => orderedInterval (-3817270202 / 1000000000000) (-3817270082 / 1000000000000)
      | _ => orderedInterval (-19940185933 / 1000000000000) (-19940185665 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9508309689 / 1000000000000) (9508309715 / 1000000000000)
      | 1 => orderedInterval (-15692437734 / 1000000000000) (-15692437645 / 1000000000000)
      | 2 => orderedInterval (-22646062478 / 1000000000000) (-22646061997 / 1000000000000)
      | 3 => orderedInterval (132578417749 / 1000000000000) (132578423523 / 1000000000000)
      | 4 => orderedInterval (-24601046944 / 1000000000000) (-24601025217 / 1000000000000)
      | 5 => orderedInterval (17493149751 / 1000000000000) (17493156700 / 1000000000000)
      | 6 => orderedInterval (11637093299 / 1000000000000) (11637093451 / 1000000000000)
      | 7 => orderedInterval (4230847860 / 1000000000000) (4230847961 / 1000000000000)
      | _ => orderedInterval (12712400286 / 1000000000000) (12712400696 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (32187821400 / 1000000000000) (32187830005 / 1000000000000)
    | 1 => orderedInterval (45200716564 / 1000000000000) (45200728416 / 1000000000000)
    | 2 => orderedInterval (-48957419116 / 1000000000000) (-48957402315 / 1000000000000)
    | 3 => orderedInterval (-136301738532 / 1000000000000) (-136301714322 / 1000000000000)
    | _ => orderedInterval (125220671478 / 1000000000000) (125220707187 / 1000000000000)

theorem compactCertificate328_stateChecks0 :
    compactCertificate328.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (401 / 2)) (orderedInterval (12453299390 / 1000000000000) (12453299391 / 1000000000000), orderedInterval (54924246437 / 1000000000000) (54924246438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (590749570108301 / 4000000000000)) (orderedInterval (-47872739195 / 1000000000000) (-47872739194 / 1000000000000), orderedInterval (-44768864391 / 1000000000000) (-44768864390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (191036273257133 / 800000000000)) (orderedInterval (37722104447 / 1000000000000) (37722104448 / 1000000000000), orderedInterval (35177311965 / 1000000000000) (35177311966 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks1 :
    compactCertificate328.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (172379251207207 / 4000000000000)) (orderedInterval (-12736381632 / 1000000000000) (-12736381582 / 1000000000000), orderedInterval (121024939499 / 1000000000000) (121024939549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (463034915889979 / 4000000000000)) (orderedInterval (-22206987513 / 1000000000000) (-22206987512 / 1000000000000), orderedInterval (-70660226453 / 1000000000000) (-70660226452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1257229869760143 / 4000000000000)) (orderedInterval (36163025611 / 1000000000000) (36163025612 / 1000000000000), orderedInterval (26732451635 / 1000000000000) (26732451636 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks2 :
    compactCertificate328.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (926069831780359 / 4000000000000)) (orderedInterval (-9157806870 / 1000000000000) (-9157806834 / 1000000000000), orderedInterval (51652234980 / 1000000000000) (51652235015 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1586836441110307 / 4000000000000)) (orderedInterval (39922355036 / 1000000000000) (39922355802 / 1000000000000), orderedInterval (-3360357379 / 1000000000000) (-3360356612 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1168856540420713 / 4000000000000)) (orderedInterval (-34474455958 / 1000000000000) (-34474455957 / 1000000000000), orderedInterval (-31407162492 / 1000000000000) (-31407162491 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks3 :
    compactCertificate328.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1793326517954599 / 4000000000000)) (orderedInterval (4922329895 / 1000000000000) (4922329899 / 1000000000000), orderedInterval (-37365182726 / 1000000000000) (-37365182723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1035377547885871 / 4000000000000)) (orderedInterval (44700876215 / 1000000000000) (44700894452 / 1000000000000), orderedInterval (-21564182627 / 1000000000000) (-21564164390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1837295627863739 / 4000000000000)) (orderedInterval (36893728287 / 1000000000000) (36893728352 / 1000000000000), orderedInterval (4944328387 / 1000000000000) (4944328453 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks4 :
    compactCertificate328.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1716639903270791 / 4000000000000)) (orderedInterval (16860517558 / 1000000000000) (16860517975 / 1000000000000), orderedInterval (-34648137355 / 1000000000000) (-34648136938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1225075235784503 / 4000000000000)) (orderedInterval (-33405263953 / 1000000000000) (-33405223292 / 1000000000000), orderedInterval (31082247933 / 1000000000000) (31082288594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1389104747669937 / 4000000000000)) (orderedInterval (26100523614 / 1000000000000) (26100530354 / 1000000000000), orderedInterval (-33977868041 / 1000000000000) (-33977861301 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks5 :
    compactCertificate328.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1158090717157153 / 4000000000000)) (orderedInterval (44938298302 / 1000000000000) (44938298304 / 1000000000000), orderedInterval (13316659095 / 1000000000000) (13316659097 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1023208269976213 / 4000000000000)) (orderedInterval (-42603409194 / 1000000000000) (-42603364388 / 1000000000000), orderedInterval (26038392412 / 1000000000000) (26038437218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (296565638097087 / 800000000000)) (orderedInterval (29266971563 / 1000000000000) (29266971564 / 1000000000000), orderedInterval (29299180570 / 1000000000000) (29299180571 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks6 :
    compactCertificate328.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (820316162370989 / 4000000000000)) (orderedInterval (-55492800321 / 1000000000000) (-55492800076 / 1000000000000), orderedInterval (5115803086 / 1000000000000) (5115803331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (695391095594629 / 4000000000000)) (orderedInterval (-58255437654 / 1000000000000) (-58255435726 / 1000000000000), orderedInterval (16545248682 / 1000000000000) (16545250610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (435143459579287 / 4000000000000)) (orderedInterval (28774194466 / 1000000000000) (28774195776 / 1000000000000), orderedInterval (-71013382033 / 1000000000000) (-71013380723 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks7 :
    compactCertificate328.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (234021599783529 / 4000000000000)) (orderedInterval (40774526378 / 1000000000000) (40774528460 / 1000000000000), orderedInterval (-96364580647 / 1000000000000) (-96364578565 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (635414167097587 / 4000000000000)) (orderedInterval (34855372785 / 1000000000000) (34855381276 / 1000000000000), orderedInterval (-52955713957 / 1000000000000) (-52955705466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (867603721943699 / 4000000000000)) (orderedInterval (-42966423407 / 1000000000000) (-42966423406 / 1000000000000), orderedInterval (-32900289174 / 1000000000000) (-32900289173 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_stateChecks8 :
    compactCertificate328.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (366856540420713 / 4000000000000)) (orderedInterval (-81985737038 / 1000000000000) (-81985737036 / 1000000000000), orderedInterval (-14371646099 / 1000000000000) (-14371646097 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1491251469544073 / 4000000000000)) (orderedInterval (10287403606 / 1000000000000) (10287403644 / 1000000000000), orderedInterval (-40036075748 / 1000000000000) (-40036075710 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (996086871002407 / 4000000000000)) (orderedInterval (-50498439928 / 1000000000000) (-50498439734 / 1000000000000), orderedInterval (2628324855 / 1000000000000) (2628325049 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_states : ∀ j,
    BesselStateValid (compactCertificate328.point j) (compactCertificate328.state j) :=
  compactCertificate328.statesValid_of_checks3 compactCertificate328_stateChecks0
    compactCertificate328_stateChecks1 compactCertificate328_stateChecks2
    compactCertificate328_stateChecks3 compactCertificate328_stateChecks4
    compactCertificate328_stateChecks5 compactCertificate328_stateChecks6
    compactCertificate328_stateChecks7 compactCertificate328_stateChecks8

theorem compactCertificate328_chunkChecks0_0 :
    compactCertificate328.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (401 / 2) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12453299390 / 1000000000000) (12453299391 / 1000000000000), orderedInterval (54924246437 / 1000000000000) (54924246438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (590749570108301 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872739195 / 1000000000000) (-47872739194 / 1000000000000), orderedInterval (-44768864391 / 1000000000000) (-44768864390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (191036273257133 / 800000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37722104447 / 1000000000000) (37722104448 / 1000000000000), orderedInterval (35177311965 / 1000000000000) (35177311966 / 1000000000000)))) (orderedInterval (6703546954 / 1000000000000) (6703546969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (172379251207207 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12736381632 / 1000000000000) (-12736381582 / 1000000000000), orderedInterval (121024939499 / 1000000000000) (121024939549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (463034915889979 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22206987513 / 1000000000000) (-22206987512 / 1000000000000), orderedInterval (-70660226453 / 1000000000000) (-70660226452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1257229869760143 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36163025611 / 1000000000000) (36163025612 / 1000000000000), orderedInterval (26732451635 / 1000000000000) (26732451636 / 1000000000000)))) (orderedInterval (-3243451698 / 1000000000000) (-3243451673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (926069831780359 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9157806870 / 1000000000000) (-9157806834 / 1000000000000), orderedInterval (51652234980 / 1000000000000) (51652235015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1586836441110307 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (39922355036 / 1000000000000) (39922355802 / 1000000000000), orderedInterval (-3360357379 / 1000000000000) (-3360356612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1168856540420713 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34474455958 / 1000000000000) (-34474455957 / 1000000000000), orderedInterval (-31407162492 / 1000000000000) (-31407162491 / 1000000000000)))) (orderedInterval (-2064544771 / 1000000000000) (-2064544735 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks0_1 :
    compactCertificate328.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1793326517954599 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4922329895 / 1000000000000) (4922329899 / 1000000000000), orderedInterval (-37365182726 / 1000000000000) (-37365182723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1035377547885871 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44700876215 / 1000000000000) (44700894452 / 1000000000000), orderedInterval (-21564182627 / 1000000000000) (-21564164390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1837295627863739 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36893728287 / 1000000000000) (36893728352 / 1000000000000), orderedInterval (4944328387 / 1000000000000) (4944328453 / 1000000000000)))) (orderedInterval (7681989307 / 1000000000000) (7681990748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1716639903270791 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16860517558 / 1000000000000) (16860517975 / 1000000000000), orderedInterval (-34648137355 / 1000000000000) (-34648136938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1225075235784503 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33405263953 / 1000000000000) (-33405223292 / 1000000000000), orderedInterval (31082247933 / 1000000000000) (31082288594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1389104747669937 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26100523614 / 1000000000000) (26100530354 / 1000000000000), orderedInterval (-33977868041 / 1000000000000) (-33977861301 / 1000000000000)))) (orderedInterval (-3595365610 / 1000000000000) (-3595361698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1158090717157153 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44938298302 / 1000000000000) (44938298304 / 1000000000000), orderedInterval (13316659095 / 1000000000000) (13316659097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1023208269976213 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-42603409194 / 1000000000000) (-42603364388 / 1000000000000), orderedInterval (26038392412 / 1000000000000) (26038437218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (296565638097087 / 800000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29266971563 / 1000000000000) (29266971564 / 1000000000000), orderedInterval (29299180570 / 1000000000000) (29299180571 / 1000000000000)))) (orderedInterval (3706331679 / 1000000000000) (3706334263 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks0_2 :
    compactCertificate328.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (820316162370989 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55492800321 / 1000000000000) (-55492800076 / 1000000000000), orderedInterval (5115803086 / 1000000000000) (5115803331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (695391095594629 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58255437654 / 1000000000000) (-58255435726 / 1000000000000), orderedInterval (16545248682 / 1000000000000) (16545250610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (435143459579287 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28774194466 / 1000000000000) (28774195776 / 1000000000000), orderedInterval (-71013382033 / 1000000000000) (-71013380723 / 1000000000000)))) (orderedInterval (13106886090 / 1000000000000) (13106886331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (234021599783529 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (40774526378 / 1000000000000) (40774528460 / 1000000000000), orderedInterval (-96364580647 / 1000000000000) (-96364578565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (635414167097587 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34855372785 / 1000000000000) (34855381276 / 1000000000000), orderedInterval (-52955713957 / 1000000000000) (-52955705466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (867603721943699 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42966423407 / 1000000000000) (-42966423406 / 1000000000000), orderedInterval (-32900289174 / 1000000000000) (-32900289173 / 1000000000000)))) (orderedInterval (1749232462 / 1000000000000) (1749232718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (366856540420713 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81985737038 / 1000000000000) (-81985737036 / 1000000000000), orderedInterval (-14371646099 / 1000000000000) (-14371646097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1491251469544073 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10287403606 / 1000000000000) (10287403644 / 1000000000000), orderedInterval (-40036075748 / 1000000000000) (-40036075710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (996086871002407 / 4000000000000) 0 (IntervalRat.scale (401 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50498439928 / 1000000000000) (-50498439734 / 1000000000000), orderedInterval (2628324855 / 1000000000000) (2628325049 / 1000000000000)))) (orderedInterval (8143196987 / 1000000000000) (8143197082 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks0 :
    compactCertificate328.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate328.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate328_chunkChecks0_0
    compactCertificate328_chunkChecks0_1 compactCertificate328_chunkChecks0_2

theorem compactCertificate328_chunkChecks1_0 :
    compactCertificate328.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (401 / 2) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12453299390 / 1000000000000) (12453299391 / 1000000000000), orderedInterval (54924246437 / 1000000000000) (54924246438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (590749570108301 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872739195 / 1000000000000) (-47872739194 / 1000000000000), orderedInterval (-44768864391 / 1000000000000) (-44768864390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (191036273257133 / 800000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37722104447 / 1000000000000) (37722104448 / 1000000000000), orderedInterval (35177311965 / 1000000000000) (35177311966 / 1000000000000)))) (orderedInterval (23921285029 / 1000000000000) (23921285046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (172379251207207 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12736381632 / 1000000000000) (-12736381582 / 1000000000000), orderedInterval (121024939499 / 1000000000000) (121024939549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (463034915889979 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22206987513 / 1000000000000) (-22206987512 / 1000000000000), orderedInterval (-70660226453 / 1000000000000) (-70660226452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1257229869760143 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36163025611 / 1000000000000) (36163025612 / 1000000000000), orderedInterval (26732451635 / 1000000000000) (26732451636 / 1000000000000)))) (orderedInterval (-4750844084 / 1000000000000) (-4750844056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (926069831780359 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9157806870 / 1000000000000) (-9157806834 / 1000000000000), orderedInterval (51652234980 / 1000000000000) (51652235015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1586836441110307 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (39922355036 / 1000000000000) (39922355802 / 1000000000000), orderedInterval (-3360357379 / 1000000000000) (-3360356612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1168856540420713 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34474455958 / 1000000000000) (-34474455957 / 1000000000000), orderedInterval (-31407162492 / 1000000000000) (-31407162491 / 1000000000000)))) (orderedInterval (-901183274 / 1000000000000) (-901183207 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks1_1 :
    compactCertificate328.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1793326517954599 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4922329895 / 1000000000000) (4922329899 / 1000000000000), orderedInterval (-37365182726 / 1000000000000) (-37365182723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1035377547885871 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44700876215 / 1000000000000) (44700894452 / 1000000000000), orderedInterval (-21564182627 / 1000000000000) (-21564164390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1837295627863739 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36893728287 / 1000000000000) (36893728352 / 1000000000000), orderedInterval (4944328387 / 1000000000000) (4944328453 / 1000000000000)))) (orderedInterval (14393549923 / 1000000000000) (14393551855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1716639903270791 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16860517558 / 1000000000000) (16860517975 / 1000000000000), orderedInterval (-34648137355 / 1000000000000) (-34648136938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1225075235784503 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33405263953 / 1000000000000) (-33405223292 / 1000000000000), orderedInterval (31082247933 / 1000000000000) (31082288594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1389104747669937 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26100523614 / 1000000000000) (26100530354 / 1000000000000), orderedInterval (-33977868041 / 1000000000000) (-33977861301 / 1000000000000)))) (orderedInterval (6126427534 / 1000000000000) (6126433522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1158090717157153 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44938298302 / 1000000000000) (44938298304 / 1000000000000), orderedInterval (13316659095 / 1000000000000) (13316659097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1023208269976213 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-42603409194 / 1000000000000) (-42603364388 / 1000000000000), orderedInterval (26038392412 / 1000000000000) (26038437218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (296565638097087 / 800000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29266971563 / 1000000000000) (29266971564 / 1000000000000), orderedInterval (29299180570 / 1000000000000) (29299180571 / 1000000000000)))) (orderedInterval (-292030494 / 1000000000000) (-292027195 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks1_2 :
    compactCertificate328.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (820316162370989 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55492800321 / 1000000000000) (-55492800076 / 1000000000000), orderedInterval (5115803086 / 1000000000000) (5115803331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (695391095594629 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58255437654 / 1000000000000) (-58255435726 / 1000000000000), orderedInterval (16545248682 / 1000000000000) (16545250610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (435143459579287 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28774194466 / 1000000000000) (28774195776 / 1000000000000), orderedInterval (-71013382033 / 1000000000000) (-71013380723 / 1000000000000)))) (orderedInterval (-2902989782 / 1000000000000) (-2902989577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (234021599783529 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (40774526378 / 1000000000000) (40774528460 / 1000000000000), orderedInterval (-96364580647 / 1000000000000) (-96364578565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (635414167097587 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34855372785 / 1000000000000) (34855381276 / 1000000000000), orderedInterval (-52955713957 / 1000000000000) (-52955705466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (867603721943699 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42966423407 / 1000000000000) (-42966423406 / 1000000000000), orderedInterval (-32900289174 / 1000000000000) (-32900289173 / 1000000000000)))) (orderedInterval (4198767441 / 1000000000000) (4198767628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (366856540420713 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81985737038 / 1000000000000) (-81985737036 / 1000000000000), orderedInterval (-14371646099 / 1000000000000) (-14371646097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1491251469544073 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10287403606 / 1000000000000) (10287403644 / 1000000000000), orderedInterval (-40036075748 / 1000000000000) (-40036075710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (996086871002407 / 4000000000000) 1 (IntervalRat.scale (401 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50498439928 / 1000000000000) (-50498439734 / 1000000000000), orderedInterval (2628324855 / 1000000000000) (2628325049 / 1000000000000)))) (orderedInterval (5407734271 / 1000000000000) (5407734400 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks1 :
    compactCertificate328.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate328.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate328_chunkChecks1_0
    compactCertificate328_chunkChecks1_1 compactCertificate328_chunkChecks1_2

theorem compactCertificate328_chunkChecks2_0 :
    compactCertificate328.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (401 / 2) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12453299390 / 1000000000000) (12453299391 / 1000000000000), orderedInterval (54924246437 / 1000000000000) (54924246438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (590749570108301 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872739195 / 1000000000000) (-47872739194 / 1000000000000), orderedInterval (-44768864391 / 1000000000000) (-44768864390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (191036273257133 / 800000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37722104447 / 1000000000000) (37722104448 / 1000000000000), orderedInterval (35177311965 / 1000000000000) (35177311966 / 1000000000000)))) (orderedInterval (-7953240064 / 1000000000000) (-7953240045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (172379251207207 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12736381632 / 1000000000000) (-12736381582 / 1000000000000), orderedInterval (121024939499 / 1000000000000) (121024939549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (463034915889979 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22206987513 / 1000000000000) (-22206987512 / 1000000000000), orderedInterval (-70660226453 / 1000000000000) (-70660226452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1257229869760143 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36163025611 / 1000000000000) (36163025612 / 1000000000000), orderedInterval (26732451635 / 1000000000000) (26732451636 / 1000000000000)))) (orderedInterval (6605177458 / 1000000000000) (6605177497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (926069831780359 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9157806870 / 1000000000000) (-9157806834 / 1000000000000), orderedInterval (51652234980 / 1000000000000) (51652235015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1586836441110307 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (39922355036 / 1000000000000) (39922355802 / 1000000000000), orderedInterval (-3360357379 / 1000000000000) (-3360356612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1168856540420713 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34474455958 / 1000000000000) (-34474455957 / 1000000000000), orderedInterval (-31407162492 / 1000000000000) (-31407162491 / 1000000000000)))) (orderedInterval (6594861308 / 1000000000000) (6594861436 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks2_1 :
    compactCertificate328.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1793326517954599 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4922329895 / 1000000000000) (4922329899 / 1000000000000), orderedInterval (-37365182726 / 1000000000000) (-37365182723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1035377547885871 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44700876215 / 1000000000000) (44700894452 / 1000000000000), orderedInterval (-21564182627 / 1000000000000) (-21564164390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1837295627863739 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36893728287 / 1000000000000) (36893728352 / 1000000000000), orderedInterval (4944328387 / 1000000000000) (4944328453 / 1000000000000)))) (orderedInterval (-28743506746 / 1000000000000) (-28743504079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1716639903270791 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16860517558 / 1000000000000) (16860517975 / 1000000000000), orderedInterval (-34648137355 / 1000000000000) (-34648136938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1225075235784503 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33405263953 / 1000000000000) (-33405223292 / 1000000000000), orderedInterval (31082247933 / 1000000000000) (31082288594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1389104747669937 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26100523614 / 1000000000000) (26100530354 / 1000000000000), orderedInterval (-33977868041 / 1000000000000) (-33977861301 / 1000000000000)))) (orderedInterval (9130990462 / 1000000000000) (9130999665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1158090717157153 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44938298302 / 1000000000000) (44938298304 / 1000000000000), orderedInterval (13316659095 / 1000000000000) (13316659097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1023208269976213 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-42603409194 / 1000000000000) (-42603364388 / 1000000000000), orderedInterval (26038392412 / 1000000000000) (26038437218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (296565638097087 / 800000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29266971563 / 1000000000000) (29266971564 / 1000000000000), orderedInterval (29299180570 / 1000000000000) (29299180571 / 1000000000000)))) (orderedInterval (-7610693342 / 1000000000000) (-7610689109 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks2_2 :
    compactCertificate328.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (820316162370989 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55492800321 / 1000000000000) (-55492800076 / 1000000000000), orderedInterval (5115803086 / 1000000000000) (5115803331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (695391095594629 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58255437654 / 1000000000000) (-58255435726 / 1000000000000), orderedInterval (16545248682 / 1000000000000) (16545250610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (435143459579287 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28774194466 / 1000000000000) (28774195776 / 1000000000000), orderedInterval (-71013382033 / 1000000000000) (-71013380723 / 1000000000000)))) (orderedInterval (-12022991589 / 1000000000000) (-12022991407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (234021599783529 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (40774526378 / 1000000000000) (40774528460 / 1000000000000), orderedInterval (-96364580647 / 1000000000000) (-96364578565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (635414167097587 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34855372785 / 1000000000000) (34855381276 / 1000000000000), orderedInterval (-52955713957 / 1000000000000) (-52955705466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (867603721943699 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42966423407 / 1000000000000) (-42966423406 / 1000000000000), orderedInterval (-32900289174 / 1000000000000) (-32900289173 / 1000000000000)))) (orderedInterval (-3314111404 / 1000000000000) (-3314111257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (366856540420713 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81985737038 / 1000000000000) (-81985737036 / 1000000000000), orderedInterval (-14371646099 / 1000000000000) (-14371646097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1491251469544073 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10287403606 / 1000000000000) (10287403644 / 1000000000000), orderedInterval (-40036075748 / 1000000000000) (-40036075710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (996086871002407 / 4000000000000) 2 (IntervalRat.scale (401 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50498439928 / 1000000000000) (-50498439734 / 1000000000000), orderedInterval (2628324855 / 1000000000000) (2628325049 / 1000000000000)))) (orderedInterval (-11643905199 / 1000000000000) (-11643905016 / 1000000000000))) = true
  rfl'

theorem compactCertificate328_chunkChecks2 :
    compactCertificate328.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate328.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate328_chunkChecks2_0
    compactCertificate328_chunkChecks2_1 compactCertificate328_chunkChecks2_2

theorem compactCertificate328_chunkChecks3_0 :
    compactCertificate328.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (401 / 2) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12453299390 / 1000000000000) (12453299391 / 1000000000000), orderedInterval (54924246437 / 1000000000000) (54924246438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (590749570108301 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872739195 / 1000000000000) (-47872739194 / 1000000000000), orderedInterval (-44768864391 / 1000000000000) (-44768864390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (191036273257133 / 800000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37722104447 / 1000000000000) (37722104448 / 1000000000000), orderedInterval (35177311965 / 1000000000000) (35177311966 / 1000000000000)))) (orderedInterval (-25050416700 / 1000000000000) (-25050416678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (172379251207207 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12736381632 / 1000000000000) (-12736381582 / 1000000000000), orderedInterval (121024939499 / 1000000000000) (121024939549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (463034915889979 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22206987513 / 1000000000000) (-22206987512 / 1000000000000), orderedInterval (-70660226453 / 1000000000000) (-70660226452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1257229869760143 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36163025611 / 1000000000000) (36163025612 / 1000000000000), orderedInterval (26732451635 / 1000000000000) (26732451636 / 1000000000000)))) (orderedInterval (7797410623 / 1000000000000) (7797410680 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (926069831780359 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9157806870 / 1000000000000) (-9157806834 / 1000000000000), orderedInterval (51652234980 / 1000000000000) (51652235015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1586836441110307 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (39922355036 / 1000000000000) (39922355802 / 1000000000000), orderedInterval (-3360357379 / 1000000000000) (-3360356612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1168856540420713 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34474455958 / 1000000000000) (-34474455957 / 1000000000000), orderedInterval (-31407162492 / 1000000000000) (-31407162491 / 1000000000000)))) (orderedInterval (1514041878 / 1000000000000) (1514042126 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate328_chunkChecks3_1 :
    compactCertificate328.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1793326517954599 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4922329895 / 1000000000000) (4922329899 / 1000000000000), orderedInterval (-37365182726 / 1000000000000) (-37365182723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1035377547885871 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44700876215 / 1000000000000) (44700894452 / 1000000000000), orderedInterval (-21564182627 / 1000000000000) (-21564164390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1837295627863739 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36893728287 / 1000000000000) (36893728352 / 1000000000000), orderedInterval (4944328387 / 1000000000000) (4944328453 / 1000000000000)))) (orderedInterval (-79099193787 / 1000000000000) (-79099189976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1716639903270791 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16860517558 / 1000000000000) (16860517975 / 1000000000000), orderedInterval (-34648137355 / 1000000000000) (-34648136938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1225075235784503 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33405263953 / 1000000000000) (-33405223292 / 1000000000000), orderedInterval (31082247933 / 1000000000000) (31082288594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1389104747669937 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26100523614 / 1000000000000) (26100530354 / 1000000000000), orderedInterval (-33977868041 / 1000000000000) (-33977861301 / 1000000000000)))) (orderedInterval (-17548963669 / 1000000000000) (-17548949559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1158090717157153 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44938298302 / 1000000000000) (44938298304 / 1000000000000), orderedInterval (13316659095 / 1000000000000) (13316659097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1023208269976213 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-42603409194 / 1000000000000) (-42603364388 / 1000000000000), orderedInterval (26038392412 / 1000000000000) (26038437218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (296565638097087 / 800000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29266971563 / 1000000000000) (29266971564 / 1000000000000), orderedInterval (29299180570 / 1000000000000) (29299180571 / 1000000000000)))) (orderedInterval (-2072082690 / 1000000000000) (-2072077281 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate328_chunkChecks3_2 :
    compactCertificate328.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (820316162370989 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55492800321 / 1000000000000) (-55492800076 / 1000000000000), orderedInterval (5115803086 / 1000000000000) (5115803331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (695391095594629 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58255437654 / 1000000000000) (-58255435726 / 1000000000000), orderedInterval (16545248682 / 1000000000000) (16545250610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (435143459579287 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28774194466 / 1000000000000) (28774195776 / 1000000000000), orderedInterval (-71013382033 / 1000000000000) (-71013380723 / 1000000000000)))) (orderedInterval (1914921948 / 1000000000000) (1914922113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (234021599783529 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (40774526378 / 1000000000000) (40774528460 / 1000000000000), orderedInterval (-96364580647 / 1000000000000) (-96364578565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (635414167097587 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34855372785 / 1000000000000) (34855381276 / 1000000000000), orderedInterval (-52955713957 / 1000000000000) (-52955705466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (867603721943699 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42966423407 / 1000000000000) (-42966423406 / 1000000000000), orderedInterval (-32900289174 / 1000000000000) (-32900289173 / 1000000000000)))) (orderedInterval (-3817270202 / 1000000000000) (-3817270082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (366856540420713 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81985737038 / 1000000000000) (-81985737036 / 1000000000000), orderedInterval (-14371646099 / 1000000000000) (-14371646097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1491251469544073 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10287403606 / 1000000000000) (10287403644 / 1000000000000), orderedInterval (-40036075748 / 1000000000000) (-40036075710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (996086871002407 / 4000000000000) 3 (IntervalRat.scale (401 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50498439928 / 1000000000000) (-50498439734 / 1000000000000), orderedInterval (2628324855 / 1000000000000) (2628325049 / 1000000000000)))) (orderedInterval (-19940185933 / 1000000000000) (-19940185665 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate328_chunkChecks3 :
    compactCertificate328.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate328.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate328_chunkChecks3_0
    compactCertificate328_chunkChecks3_1 compactCertificate328_chunkChecks3_2

theorem compactCertificate328_chunkChecks4_0 :
    compactCertificate328.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (401 / 2) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (12453299390 / 1000000000000) (12453299391 / 1000000000000), orderedInterval (54924246437 / 1000000000000) (54924246438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (590749570108301 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872739195 / 1000000000000) (-47872739194 / 1000000000000), orderedInterval (-44768864391 / 1000000000000) (-44768864390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (191036273257133 / 800000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37722104447 / 1000000000000) (37722104448 / 1000000000000), orderedInterval (35177311965 / 1000000000000) (35177311966 / 1000000000000)))) (orderedInterval (9508309689 / 1000000000000) (9508309715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (172379251207207 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-12736381632 / 1000000000000) (-12736381582 / 1000000000000), orderedInterval (121024939499 / 1000000000000) (121024939549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (463034915889979 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22206987513 / 1000000000000) (-22206987512 / 1000000000000), orderedInterval (-70660226453 / 1000000000000) (-70660226452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1257229869760143 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (36163025611 / 1000000000000) (36163025612 / 1000000000000), orderedInterval (26732451635 / 1000000000000) (26732451636 / 1000000000000)))) (orderedInterval (-15692437734 / 1000000000000) (-15692437645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (926069831780359 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9157806870 / 1000000000000) (-9157806834 / 1000000000000), orderedInterval (51652234980 / 1000000000000) (51652235015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1586836441110307 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (39922355036 / 1000000000000) (39922355802 / 1000000000000), orderedInterval (-3360357379 / 1000000000000) (-3360356612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1168856540420713 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34474455958 / 1000000000000) (-34474455957 / 1000000000000), orderedInterval (-31407162492 / 1000000000000) (-31407162491 / 1000000000000)))) (orderedInterval (-22646062478 / 1000000000000) (-22646061997 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate328_chunkChecks4_1 :
    compactCertificate328.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1793326517954599 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4922329895 / 1000000000000) (4922329899 / 1000000000000), orderedInterval (-37365182726 / 1000000000000) (-37365182723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1035377547885871 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (44700876215 / 1000000000000) (44700894452 / 1000000000000), orderedInterval (-21564182627 / 1000000000000) (-21564164390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1837295627863739 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (36893728287 / 1000000000000) (36893728352 / 1000000000000), orderedInterval (4944328387 / 1000000000000) (4944328453 / 1000000000000)))) (orderedInterval (132578417749 / 1000000000000) (132578423523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1716639903270791 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16860517558 / 1000000000000) (16860517975 / 1000000000000), orderedInterval (-34648137355 / 1000000000000) (-34648136938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1225075235784503 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33405263953 / 1000000000000) (-33405223292 / 1000000000000), orderedInterval (31082247933 / 1000000000000) (31082288594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1389104747669937 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26100523614 / 1000000000000) (26100530354 / 1000000000000), orderedInterval (-33977868041 / 1000000000000) (-33977861301 / 1000000000000)))) (orderedInterval (-24601046944 / 1000000000000) (-24601025217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1158090717157153 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44938298302 / 1000000000000) (44938298304 / 1000000000000), orderedInterval (13316659095 / 1000000000000) (13316659097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1023208269976213 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-42603409194 / 1000000000000) (-42603364388 / 1000000000000), orderedInterval (26038392412 / 1000000000000) (26038437218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (296565638097087 / 800000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29266971563 / 1000000000000) (29266971564 / 1000000000000), orderedInterval (29299180570 / 1000000000000) (29299180571 / 1000000000000)))) (orderedInterval (17493149751 / 1000000000000) (17493156700 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate328_chunkChecks4_2 :
    compactCertificate328.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (820316162370989 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-55492800321 / 1000000000000) (-55492800076 / 1000000000000), orderedInterval (5115803086 / 1000000000000) (5115803331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (695391095594629 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-58255437654 / 1000000000000) (-58255435726 / 1000000000000), orderedInterval (16545248682 / 1000000000000) (16545250610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (435143459579287 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28774194466 / 1000000000000) (28774195776 / 1000000000000), orderedInterval (-71013382033 / 1000000000000) (-71013380723 / 1000000000000)))) (orderedInterval (11637093299 / 1000000000000) (11637093451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (234021599783529 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (40774526378 / 1000000000000) (40774528460 / 1000000000000), orderedInterval (-96364580647 / 1000000000000) (-96364578565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (635414167097587 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (34855372785 / 1000000000000) (34855381276 / 1000000000000), orderedInterval (-52955713957 / 1000000000000) (-52955705466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (867603721943699 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42966423407 / 1000000000000) (-42966423406 / 1000000000000), orderedInterval (-32900289174 / 1000000000000) (-32900289173 / 1000000000000)))) (orderedInterval (4230847860 / 1000000000000) (4230847961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (366856540420713 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81985737038 / 1000000000000) (-81985737036 / 1000000000000), orderedInterval (-14371646099 / 1000000000000) (-14371646097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1491251469544073 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10287403606 / 1000000000000) (10287403644 / 1000000000000), orderedInterval (-40036075748 / 1000000000000) (-40036075710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (996086871002407 / 4000000000000) 4 (IntervalRat.scale (401 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50498439928 / 1000000000000) (-50498439734 / 1000000000000), orderedInterval (2628324855 / 1000000000000) (2628325049 / 1000000000000)))) (orderedInterval (12712400286 / 1000000000000) (12712400696 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate328_chunkChecks4 :
    compactCertificate328.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate328.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate328_chunkChecks4_0
    compactCertificate328_chunkChecks4_1 compactCertificate328_chunkChecks4_2

theorem compactCertificate328_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate328.chunkCheck r b = true :=
  compactCertificate328.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate328_chunkChecks0
    · exact compactCertificate328_chunkChecks1
    · exact compactCertificate328_chunkChecks2
    · exact compactCertificate328_chunkChecks3
    · exact compactCertificate328_chunkChecks4)

theorem compactCertificate328_coefficient0 :
    compactCertificate328.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate328_coefficient1 :
    compactCertificate328.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate328_coefficient2 :
    compactCertificate328.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate328_coefficient3 :
    compactCertificate328.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate328_coefficient4 :
    compactCertificate328.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate328_coefficients : ∀ r : Fin 5,
    compactCertificate328.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate328_coefficient0
  · exact compactCertificate328_coefficient1
  · exact compactCertificate328_coefficient2
  · exact compactCertificate328_coefficient3
  · exact compactCertificate328_coefficient4

theorem compactCertificate328_lower : (1 : ℚ) ≤ compactCertificate328.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate328, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate328_proves {t : ℝ} (ht : t ∈ compactCertificate328.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate328.proves compactCertificate328_states compactCertificate328_chunks
    compactCertificate328_coefficients compactCertificate328_lower ht

end Erdos232
