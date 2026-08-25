/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate518 : CompactCertificate where
  left := 389
  right := 390
  center := 779 / 2
  grid := fun i =>
    match i.val with
    | 0 => 124
    | 1 => 91
    | 2 => 148
    | 3 => 27
    | 4 => 72
    | 5 => 194
    | 6 => 143
    | 7 => 245
    | 8 => 181
    | 9 => 277
    | 10 => 160
    | 11 => 284
    | 12 => 266
    | 13 => 189
    | 14 => 215
    | 15 => 179
    | 16 => 158
    | 17 => 229
    | 18 => 127
    | 19 => 108
    | 20 => 67
    | 21 => 36
    | 22 => 98
    | 23 => 134
    | 24 => 57
    | 25 => 231
    | _ => 154
  point := fun i =>
    match i.val with
    | 0 => 779 / 2
    | 1 => 1147615748414879 / 4000000000000
    | 2 => 371115353783807 / 800000000000
    | 3 => 334871413193053 / 4000000000000
    | 4 => 899511719397241 / 4000000000000
    | 5 => 2442349298112597 / 4000000000000
    | 6 => 1799023438795261 / 4000000000000
    | 7 => 3082657325747953 / 4000000000000
    | 8 => 2270671433884627 / 4000000000000
    | 9 => 3483793908944221 / 4000000000000
    | 10 => 2011369351129909 / 4000000000000
    | 11 => 3569210209740281 / 4000000000000
    | 12 => 3334819163710589 / 4000000000000
    | 13 => 2379884310913037 / 4000000000000
    | 14 => 2698535158191723 / 4000000000000
    | 15 => 2249757278467387 / 4000000000000
    | 16 => 1987728783819127 / 4000000000000
    | 17 => 576121277001573 / 800000000000
    | 18 => 1593581771788031 / 4000000000000
    | 19 => 1350896916379591 / 4000000000000
    | 20 => 845328566115373 / 4000000000000
    | 21 => 454620514292691 / 4000000000000
    | 22 => 1234383132591073 / 4000000000000
    | 23 => 1685444636893121 / 4000000000000
    | 24 => 712671433884627 / 4000000000000
    | 25 => 2896969812406067 / 4000000000000
    | _ => 1935041577333853 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (26887710558 / 1000000000000) (26887710559 / 1000000000000), orderedInterval (30156625808 / 1000000000000) (30156625809 / 1000000000000))
    | 1 => (orderedInterval (-45830736305 / 1000000000000) (-45830733993 / 1000000000000), orderedInterval (10964297619 / 1000000000000) (10964299931 / 1000000000000))
    | 2 => (orderedInterval (-10109088493 / 1000000000000) (-10109088465 / 1000000000000), orderedInterval (35649994062 / 1000000000000) (35649994090 / 1000000000000))
    | 3 => (orderedInterval (27533761033 / 1000000000000) (27533761738 / 1000000000000), orderedInterval (-82907108749 / 1000000000000) (-82907108045 / 1000000000000))
    | 4 => (orderedInterval (-26984873408 / 1000000000000) (-26984869893 / 1000000000000), orderedInterval (45916045461 / 1000000000000) (45916048977 / 1000000000000))
    | 5 => (orderedInterval (30518697086 / 1000000000000) (30518729862 / 1000000000000), orderedInterval (-10572183277 / 1000000000000) (-10572150501 / 1000000000000))
    | 6 => (orderedInterval (-36182831047 / 1000000000000) (-36182831040 / 1000000000000), orderedInterval (-10269020683 / 1000000000000) (-10269020676 / 1000000000000))
    | 7 => (orderedInterval (-28231878962 / 1000000000000) (-28231860734 / 1000000000000), orderedInterval (5406031517 / 1000000000000) (5406049744 / 1000000000000))
    | 8 => (orderedInterval (5838293753 / 1000000000000) (5838293756 / 1000000000000), orderedInterval (-32980587405 / 1000000000000) (-32980587403 / 1000000000000))
    | 9 => (orderedInterval (-26990263268 / 1000000000000) (-26990260836 / 1000000000000), orderedInterval (-1557914734 / 1000000000000) (-1557912302 / 1000000000000))
    | 10 => (orderedInterval (29404112017 / 1000000000000) (29404112018 / 1000000000000), orderedInterval (20006741546 / 1000000000000) (20006741547 / 1000000000000))
    | 11 => (orderedInterval (20510067358 / 1000000000000) (20510067359 / 1000000000000), orderedInterval (17099743877 / 1000000000000) (17099743878 / 1000000000000))
    | 12 => (orderedInterval (-25482203326 / 1000000000000) (-25482118812 / 1000000000000), orderedInterval (10704611523 / 1000000000000) (10704696038 / 1000000000000))
    | 13 => (orderedInterval (-29808207001 / 1000000000000) (-29808138217 / 1000000000000), orderedInterval (13496234372 / 1000000000000) (13496303155 / 1000000000000))
    | 14 => (orderedInterval (719312890 / 1000000000000) (719312891 / 1000000000000), orderedInterval (-30711039701 / 1000000000000) (-30711039700 / 1000000000000))
    | 15 => (orderedInterval (-25917771150 / 1000000000000) (-25917771149 / 1000000000000), orderedInterval (-21428291486 / 1000000000000) (-21428291485 / 1000000000000))
    | 16 => (orderedInterval (34889522914 / 1000000000000) (34889522936 / 1000000000000), orderedInterval (7953667086 / 1000000000000) (7953667108 / 1000000000000))
    | 17 => (orderedInterval (-29681071487 / 1000000000000) (-29681070483 / 1000000000000), orderedInterval (-1723472388 / 1000000000000) (-1723471384 / 1000000000000))
    | 18 => (orderedInterval (-7873533626 / 1000000000000) (-7873533625 / 1000000000000), orderedInterval (-39181547407 / 1000000000000) (-39181547406 / 1000000000000))
    | 19 => (orderedInterval (-30618965301 / 1000000000000) (-30618940791 / 1000000000000), orderedInterval (30826938586 / 1000000000000) (30826963096 / 1000000000000))
    | 20 => (orderedInterval (-54788437301 / 1000000000000) (-54788437131 / 1000000000000), orderedInterval (3390325360 / 1000000000000) (3390325531 / 1000000000000))
    | 21 => (orderedInterval (72892850591 / 1000000000000) (72892850592 / 1000000000000), orderedInterval (16647322525 / 1000000000000) (16647322526 / 1000000000000))
    | 22 => (orderedInterval (45320566029 / 1000000000000) (45320566087 / 1000000000000), orderedInterval (2926639511 / 1000000000000) (2926639569 / 1000000000000))
    | 23 => (orderedInterval (35832422772 / 1000000000000) (35832422774 / 1000000000000), orderedInterval (15020733594 / 1000000000000) (15020733595 / 1000000000000))
    | 24 => (orderedInterval (7050599452 / 1000000000000) (7050599474 / 1000000000000), orderedInterval (-59378431231 / 1000000000000) (-59378431209 / 1000000000000))
    | 25 => (orderedInterval (18647738075 / 1000000000000) (18647739153 / 1000000000000), orderedInterval (-23062312686 / 1000000000000) (-23062311608 / 1000000000000))
    | _ => (orderedInterval (24467882624 / 1000000000000) (24467882625 / 1000000000000), orderedInterval (26757249336 / 1000000000000) (26757249337 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9637080806 / 1000000000000) (9637080857 / 1000000000000)
      | 1 => orderedInterval (-3453552210 / 1000000000000) (-3453549697 / 1000000000000)
      | 2 => orderedInterval (1011883571 / 1000000000000) (1011884155 / 1000000000000)
      | 3 => orderedInterval (9890073047 / 1000000000000) (9890073634 / 1000000000000)
      | 4 => orderedInterval (-2362358763 / 1000000000000) (-2362350686 / 1000000000000)
      | 5 => orderedInterval (-3055854017 / 1000000000000) (-3055853953 / 1000000000000)
      | 6 => orderedInterval (1208296747 / 1000000000000) (1208298238 / 1000000000000)
      | 7 => orderedInterval (-5120312857 / 1000000000000) (-5120312809 / 1000000000000)
      | _ => orderedInterval (-6066279672 / 1000000000000) (-6066279476 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14519835020 / 1000000000000) (14519835069 / 1000000000000)
      | 1 => orderedInterval (2339420741 / 1000000000000) (2339424523 / 1000000000000)
      | 2 => orderedInterval (-1491599714 / 1000000000000) (-1491598563 / 1000000000000)
      | 3 => orderedInterval (8101447490 / 1000000000000) (8101448777 / 1000000000000)
      | 4 => orderedInterval (1805032657 / 1000000000000) (1805045934 / 1000000000000)
      | 5 => orderedInterval (-1019607440 / 1000000000000) (-1019607337 / 1000000000000)
      | 6 => orderedInterval (4954925627 / 1000000000000) (4954926924 / 1000000000000)
      | 7 => orderedInterval (-1387640042 / 1000000000000) (-1387639999 / 1000000000000)
      | _ => orderedInterval (-2908348824 / 1000000000000) (-2908348509 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9621457676 / 1000000000000) (-9621457626 / 1000000000000)
      | 1 => orderedInterval (5667759066 / 1000000000000) (5667764918 / 1000000000000)
      | 2 => orderedInterval (-3704873048 / 1000000000000) (-3704870776 / 1000000000000)
      | 3 => orderedInterval (-42932780923 / 1000000000000) (-42932778073 / 1000000000000)
      | 4 => orderedInterval (4475704955 / 1000000000000) (4475727281 / 1000000000000)
      | 5 => orderedInterval (6474484708 / 1000000000000) (6474484879 / 1000000000000)
      | 6 => orderedInterval (-2107633044 / 1000000000000) (-2107631910 / 1000000000000)
      | 7 => orderedInterval (3977379052 / 1000000000000) (3977379095 / 1000000000000)
      | _ => orderedInterval (12328486448 / 1000000000000) (12328486976 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15503274944 / 1000000000000) (-15503274892 / 1000000000000)
      | 1 => orderedInterval (-3241394660 / 1000000000000) (-3241385534 / 1000000000000)
      | 2 => orderedInterval (3768602789 / 1000000000000) (3768607273 / 1000000000000)
      | 3 => orderedInterval (-35400110198 / 1000000000000) (-35400103857 / 1000000000000)
      | 4 => orderedInterval (-3472761048 / 1000000000000) (-3472722635 / 1000000000000)
      | 5 => orderedInterval (1952554731 / 1000000000000) (1952555020 / 1000000000000)
      | 6 => orderedInterval (-5578733640 / 1000000000000) (-5578732648 / 1000000000000)
      | 7 => orderedInterval (1487846409 / 1000000000000) (1487846453 / 1000000000000)
      | _ => orderedInterval (-2447840950 / 1000000000000) (-2447840040 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9417577775 / 1000000000000) (9417577833 / 1000000000000)
      | 1 => orderedInterval (-13195323866 / 1000000000000) (-13195309565 / 1000000000000)
      | 2 => orderedInterval (13962937319 / 1000000000000) (13962946186 / 1000000000000)
      | 3 => orderedInterval (206435738294 / 1000000000000) (206435752463 / 1000000000000)
      | 4 => orderedInterval (-5705223540 / 1000000000000) (-5705155539 / 1000000000000)
      | 5 => orderedInterval (-15482010570 / 1000000000000) (-15482010070 / 1000000000000)
      | 6 => orderedInterval (2231526283 / 1000000000000) (2231527155 / 1000000000000)
      | 7 => orderedInterval (-4183594041 / 1000000000000) (-4183593995 / 1000000000000)
      | _ => orderedInterval (-29054880093 / 1000000000000) (-29054878487 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1688976652 / 1000000000000) (1688990263 / 1000000000000)
    | 1 => orderedInterval (24913465515 / 1000000000000) (24913486819 / 1000000000000)
    | 2 => orderedInterval (-25442930462 / 1000000000000) (-25442895236 / 1000000000000)
    | 3 => orderedInterval (-58435111511 / 1000000000000) (-58435050860 / 1000000000000)
    | _ => orderedInterval (164426747561 / 1000000000000) (164426855981 / 1000000000000)

theorem compactCertificate518_stateChecks0 :
    compactCertificate518.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (779 / 2)) (orderedInterval (26887710558 / 1000000000000) (26887710559 / 1000000000000), orderedInterval (30156625808 / 1000000000000) (30156625809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1147615748414879 / 4000000000000)) (orderedInterval (-45830736305 / 1000000000000) (-45830733993 / 1000000000000), orderedInterval (10964297619 / 1000000000000) (10964299931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (371115353783807 / 800000000000)) (orderedInterval (-10109088493 / 1000000000000) (-10109088465 / 1000000000000), orderedInterval (35649994062 / 1000000000000) (35649994090 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks1 :
    compactCertificate518.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (334871413193053 / 4000000000000)) (orderedInterval (27533761033 / 1000000000000) (27533761738 / 1000000000000), orderedInterval (-82907108749 / 1000000000000) (-82907108045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (899511719397241 / 4000000000000)) (orderedInterval (-26984873408 / 1000000000000) (-26984869893 / 1000000000000), orderedInterval (45916045461 / 1000000000000) (45916048977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2442349298112597 / 4000000000000)) (orderedInterval (30518697086 / 1000000000000) (30518729862 / 1000000000000), orderedInterval (-10572183277 / 1000000000000) (-10572150501 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks2 :
    compactCertificate518.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1799023438795261 / 4000000000000)) (orderedInterval (-36182831047 / 1000000000000) (-36182831040 / 1000000000000), orderedInterval (-10269020683 / 1000000000000) (-10269020676 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3082657325747953 / 4000000000000)) (orderedInterval (-28231878962 / 1000000000000) (-28231860734 / 1000000000000), orderedInterval (5406031517 / 1000000000000) (5406049744 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2270671433884627 / 4000000000000)) (orderedInterval (5838293753 / 1000000000000) (5838293756 / 1000000000000), orderedInterval (-32980587405 / 1000000000000) (-32980587403 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks3 :
    compactCertificate518.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (3483793908944221 / 4000000000000)) (orderedInterval (-26990263268 / 1000000000000) (-26990260836 / 1000000000000), orderedInterval (-1557914734 / 1000000000000) (-1557912302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2011369351129909 / 4000000000000)) (orderedInterval (29404112017 / 1000000000000) (29404112018 / 1000000000000), orderedInterval (20006741546 / 1000000000000) (20006741547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (3569210209740281 / 4000000000000)) (orderedInterval (20510067358 / 1000000000000) (20510067359 / 1000000000000), orderedInterval (17099743877 / 1000000000000) (17099743878 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks4 :
    compactCertificate518.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3334819163710589 / 4000000000000)) (orderedInterval (-25482203326 / 1000000000000) (-25482118812 / 1000000000000), orderedInterval (10704611523 / 1000000000000) (10704696038 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2379884310913037 / 4000000000000)) (orderedInterval (-29808207001 / 1000000000000) (-29808138217 / 1000000000000), orderedInterval (13496234372 / 1000000000000) (13496303155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2698535158191723 / 4000000000000)) (orderedInterval (719312890 / 1000000000000) (719312891 / 1000000000000), orderedInterval (-30711039701 / 1000000000000) (-30711039700 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks5 :
    compactCertificate518.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2249757278467387 / 4000000000000)) (orderedInterval (-25917771150 / 1000000000000) (-25917771149 / 1000000000000), orderedInterval (-21428291486 / 1000000000000) (-21428291485 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1987728783819127 / 4000000000000)) (orderedInterval (34889522914 / 1000000000000) (34889522936 / 1000000000000), orderedInterval (7953667086 / 1000000000000) (7953667108 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (576121277001573 / 800000000000)) (orderedInterval (-29681071487 / 1000000000000) (-29681070483 / 1000000000000), orderedInterval (-1723472388 / 1000000000000) (-1723471384 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks6 :
    compactCertificate518.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1593581771788031 / 4000000000000)) (orderedInterval (-7873533626 / 1000000000000) (-7873533625 / 1000000000000), orderedInterval (-39181547407 / 1000000000000) (-39181547406 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1350896916379591 / 4000000000000)) (orderedInterval (-30618965301 / 1000000000000) (-30618940791 / 1000000000000), orderedInterval (30826938586 / 1000000000000) (30826963096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (845328566115373 / 4000000000000)) (orderedInterval (-54788437301 / 1000000000000) (-54788437131 / 1000000000000), orderedInterval (3390325360 / 1000000000000) (3390325531 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks7 :
    compactCertificate518.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (454620514292691 / 4000000000000)) (orderedInterval (72892850591 / 1000000000000) (72892850592 / 1000000000000), orderedInterval (16647322525 / 1000000000000) (16647322526 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1234383132591073 / 4000000000000)) (orderedInterval (45320566029 / 1000000000000) (45320566087 / 1000000000000), orderedInterval (2926639511 / 1000000000000) (2926639569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1685444636893121 / 4000000000000)) (orderedInterval (35832422772 / 1000000000000) (35832422774 / 1000000000000), orderedInterval (15020733594 / 1000000000000) (15020733595 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_stateChecks8 :
    compactCertificate518.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (712671433884627 / 4000000000000)) (orderedInterval (7050599452 / 1000000000000) (7050599474 / 1000000000000), orderedInterval (-59378431231 / 1000000000000) (-59378431209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2896969812406067 / 4000000000000)) (orderedInterval (18647738075 / 1000000000000) (18647739153 / 1000000000000), orderedInterval (-23062312686 / 1000000000000) (-23062311608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1935041577333853 / 4000000000000)) (orderedInterval (24467882624 / 1000000000000) (24467882625 / 1000000000000), orderedInterval (26757249336 / 1000000000000) (26757249337 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_states : ∀ j,
    BesselStateValid (compactCertificate518.point j) (compactCertificate518.state j) :=
  compactCertificate518.statesValid_of_checks3 compactCertificate518_stateChecks0
    compactCertificate518_stateChecks1 compactCertificate518_stateChecks2
    compactCertificate518_stateChecks3 compactCertificate518_stateChecks4
    compactCertificate518_stateChecks5 compactCertificate518_stateChecks6
    compactCertificate518_stateChecks7 compactCertificate518_stateChecks8

theorem compactCertificate518_chunkChecks0_0 :
    compactCertificate518.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (779 / 2) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26887710558 / 1000000000000) (26887710559 / 1000000000000), orderedInterval (30156625808 / 1000000000000) (30156625809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1147615748414879 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45830736305 / 1000000000000) (-45830733993 / 1000000000000), orderedInterval (10964297619 / 1000000000000) (10964299931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (371115353783807 / 800000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10109088493 / 1000000000000) (-10109088465 / 1000000000000), orderedInterval (35649994062 / 1000000000000) (35649994090 / 1000000000000)))) (orderedInterval (9637080806 / 1000000000000) (9637080857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (334871413193053 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27533761033 / 1000000000000) (27533761738 / 1000000000000), orderedInterval (-82907108749 / 1000000000000) (-82907108045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (899511719397241 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26984873408 / 1000000000000) (-26984869893 / 1000000000000), orderedInterval (45916045461 / 1000000000000) (45916048977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2442349298112597 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30518697086 / 1000000000000) (30518729862 / 1000000000000), orderedInterval (-10572183277 / 1000000000000) (-10572150501 / 1000000000000)))) (orderedInterval (-3453552210 / 1000000000000) (-3453549697 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1799023438795261 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36182831047 / 1000000000000) (-36182831040 / 1000000000000), orderedInterval (-10269020683 / 1000000000000) (-10269020676 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3082657325747953 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28231878962 / 1000000000000) (-28231860734 / 1000000000000), orderedInterval (5406031517 / 1000000000000) (5406049744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2270671433884627 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5838293753 / 1000000000000) (5838293756 / 1000000000000), orderedInterval (-32980587405 / 1000000000000) (-32980587403 / 1000000000000)))) (orderedInterval (1011883571 / 1000000000000) (1011884155 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks0_1 :
    compactCertificate518.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3483793908944221 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26990263268 / 1000000000000) (-26990260836 / 1000000000000), orderedInterval (-1557914734 / 1000000000000) (-1557912302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2011369351129909 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29404112017 / 1000000000000) (29404112018 / 1000000000000), orderedInterval (20006741546 / 1000000000000) (20006741547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3569210209740281 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20510067358 / 1000000000000) (20510067359 / 1000000000000), orderedInterval (17099743877 / 1000000000000) (17099743878 / 1000000000000)))) (orderedInterval (9890073047 / 1000000000000) (9890073634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3334819163710589 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25482203326 / 1000000000000) (-25482118812 / 1000000000000), orderedInterval (10704611523 / 1000000000000) (10704696038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2379884310913037 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29808207001 / 1000000000000) (-29808138217 / 1000000000000), orderedInterval (13496234372 / 1000000000000) (13496303155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2698535158191723 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (719312890 / 1000000000000) (719312891 / 1000000000000), orderedInterval (-30711039701 / 1000000000000) (-30711039700 / 1000000000000)))) (orderedInterval (-2362358763 / 1000000000000) (-2362350686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2249757278467387 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25917771150 / 1000000000000) (-25917771149 / 1000000000000), orderedInterval (-21428291486 / 1000000000000) (-21428291485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1987728783819127 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34889522914 / 1000000000000) (34889522936 / 1000000000000), orderedInterval (7953667086 / 1000000000000) (7953667108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (576121277001573 / 800000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29681071487 / 1000000000000) (-29681070483 / 1000000000000), orderedInterval (-1723472388 / 1000000000000) (-1723471384 / 1000000000000)))) (orderedInterval (-3055854017 / 1000000000000) (-3055853953 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks0_2 :
    compactCertificate518.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1593581771788031 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7873533626 / 1000000000000) (-7873533625 / 1000000000000), orderedInterval (-39181547407 / 1000000000000) (-39181547406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1350896916379591 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30618965301 / 1000000000000) (-30618940791 / 1000000000000), orderedInterval (30826938586 / 1000000000000) (30826963096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (845328566115373 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54788437301 / 1000000000000) (-54788437131 / 1000000000000), orderedInterval (3390325360 / 1000000000000) (3390325531 / 1000000000000)))) (orderedInterval (1208296747 / 1000000000000) (1208298238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (454620514292691 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72892850591 / 1000000000000) (72892850592 / 1000000000000), orderedInterval (16647322525 / 1000000000000) (16647322526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1234383132591073 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45320566029 / 1000000000000) (45320566087 / 1000000000000), orderedInterval (2926639511 / 1000000000000) (2926639569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1685444636893121 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35832422772 / 1000000000000) (35832422774 / 1000000000000), orderedInterval (15020733594 / 1000000000000) (15020733595 / 1000000000000)))) (orderedInterval (-5120312857 / 1000000000000) (-5120312809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (712671433884627 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7050599452 / 1000000000000) (7050599474 / 1000000000000), orderedInterval (-59378431231 / 1000000000000) (-59378431209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2896969812406067 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18647738075 / 1000000000000) (18647739153 / 1000000000000), orderedInterval (-23062312686 / 1000000000000) (-23062311608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1935041577333853 / 4000000000000) 0 (IntervalRat.scale (779 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24467882624 / 1000000000000) (24467882625 / 1000000000000), orderedInterval (26757249336 / 1000000000000) (26757249337 / 1000000000000)))) (orderedInterval (-6066279672 / 1000000000000) (-6066279476 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks0 :
    compactCertificate518.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate518.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate518_chunkChecks0_0
    compactCertificate518_chunkChecks0_1 compactCertificate518_chunkChecks0_2

theorem compactCertificate518_chunkChecks1_0 :
    compactCertificate518.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (779 / 2) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26887710558 / 1000000000000) (26887710559 / 1000000000000), orderedInterval (30156625808 / 1000000000000) (30156625809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1147615748414879 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45830736305 / 1000000000000) (-45830733993 / 1000000000000), orderedInterval (10964297619 / 1000000000000) (10964299931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (371115353783807 / 800000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10109088493 / 1000000000000) (-10109088465 / 1000000000000), orderedInterval (35649994062 / 1000000000000) (35649994090 / 1000000000000)))) (orderedInterval (14519835020 / 1000000000000) (14519835069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (334871413193053 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27533761033 / 1000000000000) (27533761738 / 1000000000000), orderedInterval (-82907108749 / 1000000000000) (-82907108045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (899511719397241 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26984873408 / 1000000000000) (-26984869893 / 1000000000000), orderedInterval (45916045461 / 1000000000000) (45916048977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2442349298112597 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30518697086 / 1000000000000) (30518729862 / 1000000000000), orderedInterval (-10572183277 / 1000000000000) (-10572150501 / 1000000000000)))) (orderedInterval (2339420741 / 1000000000000) (2339424523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1799023438795261 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36182831047 / 1000000000000) (-36182831040 / 1000000000000), orderedInterval (-10269020683 / 1000000000000) (-10269020676 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3082657325747953 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28231878962 / 1000000000000) (-28231860734 / 1000000000000), orderedInterval (5406031517 / 1000000000000) (5406049744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2270671433884627 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5838293753 / 1000000000000) (5838293756 / 1000000000000), orderedInterval (-32980587405 / 1000000000000) (-32980587403 / 1000000000000)))) (orderedInterval (-1491599714 / 1000000000000) (-1491598563 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks1_1 :
    compactCertificate518.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3483793908944221 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26990263268 / 1000000000000) (-26990260836 / 1000000000000), orderedInterval (-1557914734 / 1000000000000) (-1557912302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2011369351129909 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29404112017 / 1000000000000) (29404112018 / 1000000000000), orderedInterval (20006741546 / 1000000000000) (20006741547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3569210209740281 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20510067358 / 1000000000000) (20510067359 / 1000000000000), orderedInterval (17099743877 / 1000000000000) (17099743878 / 1000000000000)))) (orderedInterval (8101447490 / 1000000000000) (8101448777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3334819163710589 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25482203326 / 1000000000000) (-25482118812 / 1000000000000), orderedInterval (10704611523 / 1000000000000) (10704696038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2379884310913037 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29808207001 / 1000000000000) (-29808138217 / 1000000000000), orderedInterval (13496234372 / 1000000000000) (13496303155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2698535158191723 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (719312890 / 1000000000000) (719312891 / 1000000000000), orderedInterval (-30711039701 / 1000000000000) (-30711039700 / 1000000000000)))) (orderedInterval (1805032657 / 1000000000000) (1805045934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2249757278467387 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25917771150 / 1000000000000) (-25917771149 / 1000000000000), orderedInterval (-21428291486 / 1000000000000) (-21428291485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1987728783819127 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34889522914 / 1000000000000) (34889522936 / 1000000000000), orderedInterval (7953667086 / 1000000000000) (7953667108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (576121277001573 / 800000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29681071487 / 1000000000000) (-29681070483 / 1000000000000), orderedInterval (-1723472388 / 1000000000000) (-1723471384 / 1000000000000)))) (orderedInterval (-1019607440 / 1000000000000) (-1019607337 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks1_2 :
    compactCertificate518.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1593581771788031 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7873533626 / 1000000000000) (-7873533625 / 1000000000000), orderedInterval (-39181547407 / 1000000000000) (-39181547406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1350896916379591 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30618965301 / 1000000000000) (-30618940791 / 1000000000000), orderedInterval (30826938586 / 1000000000000) (30826963096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (845328566115373 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54788437301 / 1000000000000) (-54788437131 / 1000000000000), orderedInterval (3390325360 / 1000000000000) (3390325531 / 1000000000000)))) (orderedInterval (4954925627 / 1000000000000) (4954926924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (454620514292691 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72892850591 / 1000000000000) (72892850592 / 1000000000000), orderedInterval (16647322525 / 1000000000000) (16647322526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1234383132591073 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45320566029 / 1000000000000) (45320566087 / 1000000000000), orderedInterval (2926639511 / 1000000000000) (2926639569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1685444636893121 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35832422772 / 1000000000000) (35832422774 / 1000000000000), orderedInterval (15020733594 / 1000000000000) (15020733595 / 1000000000000)))) (orderedInterval (-1387640042 / 1000000000000) (-1387639999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (712671433884627 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7050599452 / 1000000000000) (7050599474 / 1000000000000), orderedInterval (-59378431231 / 1000000000000) (-59378431209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2896969812406067 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18647738075 / 1000000000000) (18647739153 / 1000000000000), orderedInterval (-23062312686 / 1000000000000) (-23062311608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1935041577333853 / 4000000000000) 1 (IntervalRat.scale (779 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24467882624 / 1000000000000) (24467882625 / 1000000000000), orderedInterval (26757249336 / 1000000000000) (26757249337 / 1000000000000)))) (orderedInterval (-2908348824 / 1000000000000) (-2908348509 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks1 :
    compactCertificate518.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate518.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate518_chunkChecks1_0
    compactCertificate518_chunkChecks1_1 compactCertificate518_chunkChecks1_2

theorem compactCertificate518_chunkChecks2_0 :
    compactCertificate518.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (779 / 2) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26887710558 / 1000000000000) (26887710559 / 1000000000000), orderedInterval (30156625808 / 1000000000000) (30156625809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1147615748414879 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45830736305 / 1000000000000) (-45830733993 / 1000000000000), orderedInterval (10964297619 / 1000000000000) (10964299931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (371115353783807 / 800000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10109088493 / 1000000000000) (-10109088465 / 1000000000000), orderedInterval (35649994062 / 1000000000000) (35649994090 / 1000000000000)))) (orderedInterval (-9621457676 / 1000000000000) (-9621457626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (334871413193053 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27533761033 / 1000000000000) (27533761738 / 1000000000000), orderedInterval (-82907108749 / 1000000000000) (-82907108045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (899511719397241 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26984873408 / 1000000000000) (-26984869893 / 1000000000000), orderedInterval (45916045461 / 1000000000000) (45916048977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2442349298112597 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30518697086 / 1000000000000) (30518729862 / 1000000000000), orderedInterval (-10572183277 / 1000000000000) (-10572150501 / 1000000000000)))) (orderedInterval (5667759066 / 1000000000000) (5667764918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1799023438795261 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36182831047 / 1000000000000) (-36182831040 / 1000000000000), orderedInterval (-10269020683 / 1000000000000) (-10269020676 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3082657325747953 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28231878962 / 1000000000000) (-28231860734 / 1000000000000), orderedInterval (5406031517 / 1000000000000) (5406049744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2270671433884627 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5838293753 / 1000000000000) (5838293756 / 1000000000000), orderedInterval (-32980587405 / 1000000000000) (-32980587403 / 1000000000000)))) (orderedInterval (-3704873048 / 1000000000000) (-3704870776 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks2_1 :
    compactCertificate518.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3483793908944221 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26990263268 / 1000000000000) (-26990260836 / 1000000000000), orderedInterval (-1557914734 / 1000000000000) (-1557912302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2011369351129909 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29404112017 / 1000000000000) (29404112018 / 1000000000000), orderedInterval (20006741546 / 1000000000000) (20006741547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3569210209740281 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20510067358 / 1000000000000) (20510067359 / 1000000000000), orderedInterval (17099743877 / 1000000000000) (17099743878 / 1000000000000)))) (orderedInterval (-42932780923 / 1000000000000) (-42932778073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3334819163710589 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25482203326 / 1000000000000) (-25482118812 / 1000000000000), orderedInterval (10704611523 / 1000000000000) (10704696038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2379884310913037 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29808207001 / 1000000000000) (-29808138217 / 1000000000000), orderedInterval (13496234372 / 1000000000000) (13496303155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2698535158191723 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (719312890 / 1000000000000) (719312891 / 1000000000000), orderedInterval (-30711039701 / 1000000000000) (-30711039700 / 1000000000000)))) (orderedInterval (4475704955 / 1000000000000) (4475727281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2249757278467387 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25917771150 / 1000000000000) (-25917771149 / 1000000000000), orderedInterval (-21428291486 / 1000000000000) (-21428291485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1987728783819127 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34889522914 / 1000000000000) (34889522936 / 1000000000000), orderedInterval (7953667086 / 1000000000000) (7953667108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (576121277001573 / 800000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29681071487 / 1000000000000) (-29681070483 / 1000000000000), orderedInterval (-1723472388 / 1000000000000) (-1723471384 / 1000000000000)))) (orderedInterval (6474484708 / 1000000000000) (6474484879 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks2_2 :
    compactCertificate518.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1593581771788031 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7873533626 / 1000000000000) (-7873533625 / 1000000000000), orderedInterval (-39181547407 / 1000000000000) (-39181547406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1350896916379591 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30618965301 / 1000000000000) (-30618940791 / 1000000000000), orderedInterval (30826938586 / 1000000000000) (30826963096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (845328566115373 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54788437301 / 1000000000000) (-54788437131 / 1000000000000), orderedInterval (3390325360 / 1000000000000) (3390325531 / 1000000000000)))) (orderedInterval (-2107633044 / 1000000000000) (-2107631910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (454620514292691 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72892850591 / 1000000000000) (72892850592 / 1000000000000), orderedInterval (16647322525 / 1000000000000) (16647322526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1234383132591073 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45320566029 / 1000000000000) (45320566087 / 1000000000000), orderedInterval (2926639511 / 1000000000000) (2926639569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1685444636893121 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35832422772 / 1000000000000) (35832422774 / 1000000000000), orderedInterval (15020733594 / 1000000000000) (15020733595 / 1000000000000)))) (orderedInterval (3977379052 / 1000000000000) (3977379095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (712671433884627 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7050599452 / 1000000000000) (7050599474 / 1000000000000), orderedInterval (-59378431231 / 1000000000000) (-59378431209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2896969812406067 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18647738075 / 1000000000000) (18647739153 / 1000000000000), orderedInterval (-23062312686 / 1000000000000) (-23062311608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1935041577333853 / 4000000000000) 2 (IntervalRat.scale (779 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24467882624 / 1000000000000) (24467882625 / 1000000000000), orderedInterval (26757249336 / 1000000000000) (26757249337 / 1000000000000)))) (orderedInterval (12328486448 / 1000000000000) (12328486976 / 1000000000000))) = true
  rfl'

theorem compactCertificate518_chunkChecks2 :
    compactCertificate518.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate518.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate518_chunkChecks2_0
    compactCertificate518_chunkChecks2_1 compactCertificate518_chunkChecks2_2

theorem compactCertificate518_chunkChecks3_0 :
    compactCertificate518.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (779 / 2) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26887710558 / 1000000000000) (26887710559 / 1000000000000), orderedInterval (30156625808 / 1000000000000) (30156625809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1147615748414879 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45830736305 / 1000000000000) (-45830733993 / 1000000000000), orderedInterval (10964297619 / 1000000000000) (10964299931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (371115353783807 / 800000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10109088493 / 1000000000000) (-10109088465 / 1000000000000), orderedInterval (35649994062 / 1000000000000) (35649994090 / 1000000000000)))) (orderedInterval (-15503274944 / 1000000000000) (-15503274892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (334871413193053 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27533761033 / 1000000000000) (27533761738 / 1000000000000), orderedInterval (-82907108749 / 1000000000000) (-82907108045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (899511719397241 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26984873408 / 1000000000000) (-26984869893 / 1000000000000), orderedInterval (45916045461 / 1000000000000) (45916048977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2442349298112597 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30518697086 / 1000000000000) (30518729862 / 1000000000000), orderedInterval (-10572183277 / 1000000000000) (-10572150501 / 1000000000000)))) (orderedInterval (-3241394660 / 1000000000000) (-3241385534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1799023438795261 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36182831047 / 1000000000000) (-36182831040 / 1000000000000), orderedInterval (-10269020683 / 1000000000000) (-10269020676 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3082657325747953 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28231878962 / 1000000000000) (-28231860734 / 1000000000000), orderedInterval (5406031517 / 1000000000000) (5406049744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2270671433884627 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5838293753 / 1000000000000) (5838293756 / 1000000000000), orderedInterval (-32980587405 / 1000000000000) (-32980587403 / 1000000000000)))) (orderedInterval (3768602789 / 1000000000000) (3768607273 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate518_chunkChecks3_1 :
    compactCertificate518.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3483793908944221 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26990263268 / 1000000000000) (-26990260836 / 1000000000000), orderedInterval (-1557914734 / 1000000000000) (-1557912302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2011369351129909 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29404112017 / 1000000000000) (29404112018 / 1000000000000), orderedInterval (20006741546 / 1000000000000) (20006741547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3569210209740281 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20510067358 / 1000000000000) (20510067359 / 1000000000000), orderedInterval (17099743877 / 1000000000000) (17099743878 / 1000000000000)))) (orderedInterval (-35400110198 / 1000000000000) (-35400103857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3334819163710589 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25482203326 / 1000000000000) (-25482118812 / 1000000000000), orderedInterval (10704611523 / 1000000000000) (10704696038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2379884310913037 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29808207001 / 1000000000000) (-29808138217 / 1000000000000), orderedInterval (13496234372 / 1000000000000) (13496303155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2698535158191723 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (719312890 / 1000000000000) (719312891 / 1000000000000), orderedInterval (-30711039701 / 1000000000000) (-30711039700 / 1000000000000)))) (orderedInterval (-3472761048 / 1000000000000) (-3472722635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2249757278467387 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25917771150 / 1000000000000) (-25917771149 / 1000000000000), orderedInterval (-21428291486 / 1000000000000) (-21428291485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1987728783819127 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34889522914 / 1000000000000) (34889522936 / 1000000000000), orderedInterval (7953667086 / 1000000000000) (7953667108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (576121277001573 / 800000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29681071487 / 1000000000000) (-29681070483 / 1000000000000), orderedInterval (-1723472388 / 1000000000000) (-1723471384 / 1000000000000)))) (orderedInterval (1952554731 / 1000000000000) (1952555020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate518_chunkChecks3_2 :
    compactCertificate518.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1593581771788031 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7873533626 / 1000000000000) (-7873533625 / 1000000000000), orderedInterval (-39181547407 / 1000000000000) (-39181547406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1350896916379591 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30618965301 / 1000000000000) (-30618940791 / 1000000000000), orderedInterval (30826938586 / 1000000000000) (30826963096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (845328566115373 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54788437301 / 1000000000000) (-54788437131 / 1000000000000), orderedInterval (3390325360 / 1000000000000) (3390325531 / 1000000000000)))) (orderedInterval (-5578733640 / 1000000000000) (-5578732648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (454620514292691 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72892850591 / 1000000000000) (72892850592 / 1000000000000), orderedInterval (16647322525 / 1000000000000) (16647322526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1234383132591073 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45320566029 / 1000000000000) (45320566087 / 1000000000000), orderedInterval (2926639511 / 1000000000000) (2926639569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1685444636893121 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35832422772 / 1000000000000) (35832422774 / 1000000000000), orderedInterval (15020733594 / 1000000000000) (15020733595 / 1000000000000)))) (orderedInterval (1487846409 / 1000000000000) (1487846453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (712671433884627 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7050599452 / 1000000000000) (7050599474 / 1000000000000), orderedInterval (-59378431231 / 1000000000000) (-59378431209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2896969812406067 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18647738075 / 1000000000000) (18647739153 / 1000000000000), orderedInterval (-23062312686 / 1000000000000) (-23062311608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1935041577333853 / 4000000000000) 3 (IntervalRat.scale (779 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24467882624 / 1000000000000) (24467882625 / 1000000000000), orderedInterval (26757249336 / 1000000000000) (26757249337 / 1000000000000)))) (orderedInterval (-2447840950 / 1000000000000) (-2447840040 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate518_chunkChecks3 :
    compactCertificate518.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate518.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate518_chunkChecks3_0
    compactCertificate518_chunkChecks3_1 compactCertificate518_chunkChecks3_2

theorem compactCertificate518_chunkChecks4_0 :
    compactCertificate518.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (779 / 2) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26887710558 / 1000000000000) (26887710559 / 1000000000000), orderedInterval (30156625808 / 1000000000000) (30156625809 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1147615748414879 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45830736305 / 1000000000000) (-45830733993 / 1000000000000), orderedInterval (10964297619 / 1000000000000) (10964299931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (371115353783807 / 800000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10109088493 / 1000000000000) (-10109088465 / 1000000000000), orderedInterval (35649994062 / 1000000000000) (35649994090 / 1000000000000)))) (orderedInterval (9417577775 / 1000000000000) (9417577833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (334871413193053 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (27533761033 / 1000000000000) (27533761738 / 1000000000000), orderedInterval (-82907108749 / 1000000000000) (-82907108045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (899511719397241 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26984873408 / 1000000000000) (-26984869893 / 1000000000000), orderedInterval (45916045461 / 1000000000000) (45916048977 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2442349298112597 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30518697086 / 1000000000000) (30518729862 / 1000000000000), orderedInterval (-10572183277 / 1000000000000) (-10572150501 / 1000000000000)))) (orderedInterval (-13195323866 / 1000000000000) (-13195309565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1799023438795261 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36182831047 / 1000000000000) (-36182831040 / 1000000000000), orderedInterval (-10269020683 / 1000000000000) (-10269020676 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3082657325747953 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28231878962 / 1000000000000) (-28231860734 / 1000000000000), orderedInterval (5406031517 / 1000000000000) (5406049744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2270671433884627 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5838293753 / 1000000000000) (5838293756 / 1000000000000), orderedInterval (-32980587405 / 1000000000000) (-32980587403 / 1000000000000)))) (orderedInterval (13962937319 / 1000000000000) (13962946186 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate518_chunkChecks4_1 :
    compactCertificate518.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3483793908944221 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26990263268 / 1000000000000) (-26990260836 / 1000000000000), orderedInterval (-1557914734 / 1000000000000) (-1557912302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2011369351129909 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29404112017 / 1000000000000) (29404112018 / 1000000000000), orderedInterval (20006741546 / 1000000000000) (20006741547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3569210209740281 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20510067358 / 1000000000000) (20510067359 / 1000000000000), orderedInterval (17099743877 / 1000000000000) (17099743878 / 1000000000000)))) (orderedInterval (206435738294 / 1000000000000) (206435752463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3334819163710589 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25482203326 / 1000000000000) (-25482118812 / 1000000000000), orderedInterval (10704611523 / 1000000000000) (10704696038 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2379884310913037 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29808207001 / 1000000000000) (-29808138217 / 1000000000000), orderedInterval (13496234372 / 1000000000000) (13496303155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2698535158191723 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (719312890 / 1000000000000) (719312891 / 1000000000000), orderedInterval (-30711039701 / 1000000000000) (-30711039700 / 1000000000000)))) (orderedInterval (-5705223540 / 1000000000000) (-5705155539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2249757278467387 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25917771150 / 1000000000000) (-25917771149 / 1000000000000), orderedInterval (-21428291486 / 1000000000000) (-21428291485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1987728783819127 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34889522914 / 1000000000000) (34889522936 / 1000000000000), orderedInterval (7953667086 / 1000000000000) (7953667108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (576121277001573 / 800000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29681071487 / 1000000000000) (-29681070483 / 1000000000000), orderedInterval (-1723472388 / 1000000000000) (-1723471384 / 1000000000000)))) (orderedInterval (-15482010570 / 1000000000000) (-15482010070 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate518_chunkChecks4_2 :
    compactCertificate518.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1593581771788031 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-7873533626 / 1000000000000) (-7873533625 / 1000000000000), orderedInterval (-39181547407 / 1000000000000) (-39181547406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1350896916379591 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30618965301 / 1000000000000) (-30618940791 / 1000000000000), orderedInterval (30826938586 / 1000000000000) (30826963096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (845328566115373 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54788437301 / 1000000000000) (-54788437131 / 1000000000000), orderedInterval (3390325360 / 1000000000000) (3390325531 / 1000000000000)))) (orderedInterval (2231526283 / 1000000000000) (2231527155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (454620514292691 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (72892850591 / 1000000000000) (72892850592 / 1000000000000), orderedInterval (16647322525 / 1000000000000) (16647322526 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1234383132591073 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45320566029 / 1000000000000) (45320566087 / 1000000000000), orderedInterval (2926639511 / 1000000000000) (2926639569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1685444636893121 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35832422772 / 1000000000000) (35832422774 / 1000000000000), orderedInterval (15020733594 / 1000000000000) (15020733595 / 1000000000000)))) (orderedInterval (-4183594041 / 1000000000000) (-4183593995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (712671433884627 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (7050599452 / 1000000000000) (7050599474 / 1000000000000), orderedInterval (-59378431231 / 1000000000000) (-59378431209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2896969812406067 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (18647738075 / 1000000000000) (18647739153 / 1000000000000), orderedInterval (-23062312686 / 1000000000000) (-23062311608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1935041577333853 / 4000000000000) 4 (IntervalRat.scale (779 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24467882624 / 1000000000000) (24467882625 / 1000000000000), orderedInterval (26757249336 / 1000000000000) (26757249337 / 1000000000000)))) (orderedInterval (-29054880093 / 1000000000000) (-29054878487 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate518_chunkChecks4 :
    compactCertificate518.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate518.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate518_chunkChecks4_0
    compactCertificate518_chunkChecks4_1 compactCertificate518_chunkChecks4_2

theorem compactCertificate518_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate518.chunkCheck r b = true :=
  compactCertificate518.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate518_chunkChecks0
    · exact compactCertificate518_chunkChecks1
    · exact compactCertificate518_chunkChecks2
    · exact compactCertificate518_chunkChecks3
    · exact compactCertificate518_chunkChecks4)

theorem compactCertificate518_coefficient0 :
    compactCertificate518.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate518_coefficient1 :
    compactCertificate518.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate518_coefficient2 :
    compactCertificate518.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate518_coefficient3 :
    compactCertificate518.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate518_coefficient4 :
    compactCertificate518.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate518_coefficients : ∀ r : Fin 5,
    compactCertificate518.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate518_coefficient0
  · exact compactCertificate518_coefficient1
  · exact compactCertificate518_coefficient2
  · exact compactCertificate518_coefficient3
  · exact compactCertificate518_coefficient4

theorem compactCertificate518_lower : (1 : ℚ) ≤ compactCertificate518.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate518, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate518_proves {t : ℝ} (ht : t ∈ compactCertificate518.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate518.proves compactCertificate518_states compactCertificate518_chunks
    compactCertificate518_coefficients compactCertificate518_lower ht

end Erdos232
