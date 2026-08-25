/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate440 : CompactCertificate where
  left := 311
  right := 312
  center := 623 / 2
  grid := fun i =>
    match i.val with
    | 0 => 99
    | 1 => 73
    | 2 => 118
    | 3 => 21
    | 4 => 57
    | 5 => 156
    | 6 => 115
    | 7 => 196
    | 8 => 145
    | 9 => 222
    | 10 => 128
    | 11 => 227
    | 12 => 212
    | 13 => 152
    | 14 => 172
    | 15 => 143
    | 16 => 127
    | 17 => 183
    | 18 => 101
    | 19 => 86
    | 20 => 54
    | 21 => 29
    | 22 => 79
    | 23 => 107
    | 24 => 45
    | 25 => 184
    | _ => 123
  point := fun i =>
    match i.val with
    | 0 => 623 / 2
    | 1 => 917797960542323 / 4000000000000
    | 2 => 296797003090259 / 800000000000
    | 3 => 267811155865561 / 4000000000000
    | 4 => 719378435410117 / 4000000000000
    | 5 => 1953252391173489 / 4000000000000
    | 6 => 1438756870820857 / 4000000000000
    | 7 => 2465334420976861 / 4000000000000
    | 8 => 1815954176264599 / 4000000000000
    | 9 => 2786140699964377 / 4000000000000
    | 10 => 1608579083124433 / 4000000000000
    | 11 => 2854451810870597 / 4000000000000
    | 12 => 2666999151465593 / 4000000000000
    | 13 => 1903296438637769 / 4000000000000
    | 14 => 2158135306230351 / 4000000000000
    | 15 => 1799228221418719 / 4000000000000
    | 16 => 1589672698741099 / 4000000000000
    | 17 => 460749108564801 / 800000000000
    | 18 => 1274456282187347 / 4000000000000
    | 19 => 1080370704627067 / 4000000000000
    | 20 => 676045823735401 / 4000000000000
    | 21 => 363579692431767 / 4000000000000
    | 22 => 987189591276301 / 4000000000000
    | 23 => 1347922989453677 / 4000000000000
    | 24 => 569954176264599 / 4000000000000
    | 25 => 2316832083605879 / 4000000000000
    | _ => 1547536460435161 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-43141753448 / 1000000000000) (-43141753446 / 1000000000000), orderedInterval (-13440382891 / 1000000000000) (-13440382889 / 1000000000000))
    | 1 => (orderedInterval (-41197984794 / 1000000000000) (-41197984793 / 1000000000000), orderedInterval (-32732131754 / 1000000000000) (-32732131753 / 1000000000000))
    | 2 => (orderedInterval (36404465948 / 1000000000000) (36404465949 / 1000000000000), orderedInterval (19716755873 / 1000000000000) (19716755874 / 1000000000000))
    | 3 => (orderedInterval (-95716866709 / 1000000000000) (-95716866329 / 1000000000000), orderedInterval (19329909337 / 1000000000000) (19329909717 / 1000000000000))
    | 4 => (orderedInterval (-59491900260 / 1000000000000) (-59491900210 / 1000000000000), orderedInterval (-564346434 / 1000000000000) (-564346384 / 1000000000000))
    | 5 => (orderedInterval (-30190621977 / 1000000000000) (-30190543218 / 1000000000000), orderedInterval (19835938973 / 1000000000000) (19836017732 / 1000000000000))
    | 6 => (orderedInterval (30438691999 / 1000000000000) (30438720167 / 1000000000000), orderedInterval (-29083697704 / 1000000000000) (-29083669536 / 1000000000000))
    | 7 => (orderedInterval (31471531358 / 1000000000000) (31471531433 / 1000000000000), orderedInterval (6490346557 / 1000000000000) (6490346632 / 1000000000000))
    | 8 => (orderedInterval (25723808490 / 1000000000000) (25723819394 / 1000000000000), orderedInterval (-27241697172 / 1000000000000) (-27241686268 / 1000000000000))
    | 9 => (orderedInterval (-3414231823 / 1000000000000) (-3414231822 / 1000000000000), orderedInterval (30041159971 / 1000000000000) (30041159972 / 1000000000000))
    | 10 => (orderedInterval (28707703528 / 1000000000000) (28707703529 / 1000000000000), orderedInterval (27512970666 / 1000000000000) (27512970667 / 1000000000000))
    | 11 => (orderedInterval (-28406377839 / 1000000000000) (-28406377808 / 1000000000000), orderedInterval (-9209693197 / 1000000000000) (-9209693166 / 1000000000000))
    | 12 => (orderedInterval (30855892457 / 1000000000000) (30855893230 / 1000000000000), orderedInterval (1627381819 / 1000000000000) (1627382592 / 1000000000000))
    | 13 => (orderedInterval (-28941873240 / 1000000000000) (-28941830833 / 1000000000000), orderedInterval (22397774608 / 1000000000000) (22397817015 / 1000000000000))
    | 14 => (orderedInterval (-1200071506 / 1000000000000) (-1200071505 / 1000000000000), orderedInterval (34330464959 / 1000000000000) (34330464960 / 1000000000000))
    | 15 => (orderedInterval (-36660895410 / 1000000000000) (-36660895394 / 1000000000000), orderedInterval (-8402909021 / 1000000000000) (-8402909006 / 1000000000000))
    | 16 => (orderedInterval (28119537061 / 1000000000000) (28119554859 / 1000000000000), orderedInterval (-28516609357 / 1000000000000) (-28516591560 / 1000000000000))
    | 17 => (orderedInterval (-32299505112 / 1000000000000) (-32299493663 / 1000000000000), orderedInterval (7908815293 / 1000000000000) (7908826742 / 1000000000000))
    | 18 => (orderedInterval (-38625608582 / 1000000000000) (-38625558752 / 1000000000000), orderedInterval (22558446582 / 1000000000000) (22558496413 / 1000000000000))
    | 19 => (orderedInterval (31300221608 / 1000000000000) (31300221609 / 1000000000000), orderedInterval (37054571778 / 1000000000000) (37054571779 / 1000000000000))
    | 20 => (orderedInterval (9178293750 / 1000000000000) (9178293752 / 1000000000000), orderedInterval (60656455009 / 1000000000000) (60656455010 / 1000000000000))
    | 21 => (orderedInterval (-45355353158 / 1000000000000) (-45355353157 / 1000000000000), orderedInterval (-70084323143 / 1000000000000) (-70084323142 / 1000000000000))
    | 22 => (orderedInterval (28825398034 / 1000000000000) (28825404691 / 1000000000000), orderedInterval (-41874929216 / 1000000000000) (-41874922559 / 1000000000000))
    | 23 => (orderedInterval (-43421606442 / 1000000000000) (-43421606117 / 1000000000000), orderedInterval (2000765904 / 1000000000000) (2000766229 / 1000000000000))
    | 24 => (orderedInterval (-63222273009 / 1000000000000) (-63222269975 / 1000000000000), orderedInterval (21919519369 / 1000000000000) (21919522403 / 1000000000000))
    | 25 => (orderedInterval (30917100821 / 1000000000000) (30917140343 / 1000000000000), orderedInterval (-11995519864 / 1000000000000) (-11995480342 / 1000000000000))
    | _ => (orderedInterval (-38537301336 / 1000000000000) (-38537301333 / 1000000000000), orderedInterval (-12614332461 / 1000000000000) (-12614332459 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15347510546 / 1000000000000) (-15347510523 / 1000000000000)
      | 1 => orderedInterval (1012541845 / 1000000000000) (1012547488 / 1000000000000)
      | 2 => orderedInterval (-349014258 / 1000000000000) (-349013974 / 1000000000000)
      | 3 => orderedInterval (-1304461675 / 1000000000000) (-1304461547 / 1000000000000)
      | 4 => orderedInterval (-3287797541 / 1000000000000) (-3287793479 / 1000000000000)
      | 5 => orderedInterval (-2859531535 / 1000000000000) (-2859530192 / 1000000000000)
      | 6 => orderedInterval (4703145548 / 1000000000000) (4703153594 / 1000000000000)
      | 7 => orderedInterval (3511316732 / 1000000000000) (3511316945 / 1000000000000)
      | _ => orderedInterval (4332785203 / 1000000000000) (4332788526 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4173970754 / 1000000000000) (-4173970728 / 1000000000000)
      | 1 => orderedInterval (-2267526126 / 1000000000000) (-2267517304 / 1000000000000)
      | 2 => orderedInterval (-1355630364 / 1000000000000) (-1355629944 / 1000000000000)
      | 3 => orderedInterval (-12303613924 / 1000000000000) (-12303613657 / 1000000000000)
      | 4 => orderedInterval (2871497624 / 1000000000000) (2871503840 / 1000000000000)
      | 5 => orderedInterval (2316306097 / 1000000000000) (2316307982 / 1000000000000)
      | 6 => orderedInterval (-4436394078 / 1000000000000) (-4436385856 / 1000000000000)
      | 7 => orderedInterval (964421201 / 1000000000000) (964421382 / 1000000000000)
      | _ => orderedInterval (4815629816 / 1000000000000) (4815635928 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14291332221 / 1000000000000) (14291332251 / 1000000000000)
      | 1 => orderedInterval (-4590873729 / 1000000000000) (-4590859882 / 1000000000000)
      | 2 => orderedInterval (2483995730 / 1000000000000) (2483996355 / 1000000000000)
      | 3 => orderedInterval (14654035618 / 1000000000000) (14654036191 / 1000000000000)
      | 4 => orderedInterval (8910590664 / 1000000000000) (8910600205 / 1000000000000)
      | 5 => orderedInterval (6321674780 / 1000000000000) (6321677511 / 1000000000000)
      | 6 => orderedInterval (-5203074431 / 1000000000000) (-5203066000 / 1000000000000)
      | 7 => orderedInterval (-3558379650 / 1000000000000) (-3558379492 / 1000000000000)
      | _ => orderedInterval (-2388140858 / 1000000000000) (-2388129531 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (3448623073 / 1000000000000) (3448623107 / 1000000000000)
      | 1 => orderedInterval (5453016170 / 1000000000000) (5453037872 / 1000000000000)
      | 2 => orderedInterval (3580803241 / 1000000000000) (3580804175 / 1000000000000)
      | 3 => orderedInterval (70987519593 / 1000000000000) (70987520850 / 1000000000000)
      | 4 => orderedInterval (-6386766310 / 1000000000000) (-6386751681 / 1000000000000)
      | 5 => orderedInterval (-4396934875 / 1000000000000) (-4396930799 / 1000000000000)
      | 6 => orderedInterval (4928156449 / 1000000000000) (4928165069 / 1000000000000)
      | 7 => orderedInterval (-299064200 / 1000000000000) (-299064058 / 1000000000000)
      | _ => orderedInterval (-10816845709 / 1000000000000) (-10816824712 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-12936562129 / 1000000000000) (-12936562089 / 1000000000000)
      | 1 => orderedInterval (12686807993 / 1000000000000) (12686842079 / 1000000000000)
      | 2 => orderedInterval (-12095174552 / 1000000000000) (-12095173140 / 1000000000000)
      | 3 => orderedInterval (-90604820572 / 1000000000000) (-90604817776 / 1000000000000)
      | 4 => orderedInterval (-26497285592 / 1000000000000) (-26497263080 / 1000000000000)
      | 5 => orderedInterval (-15740106552 / 1000000000000) (-15740100245 / 1000000000000)
      | 6 => orderedInterval (5752602693 / 1000000000000) (5752611534 / 1000000000000)
      | 7 => orderedInterval (4307948186 / 1000000000000) (4307948317 / 1000000000000)
      | _ => orderedInterval (-12826031283 / 1000000000000) (-12825992248 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9588526227 / 1000000000000) (-9588503162 / 1000000000000)
    | 1 => orderedInterval (-13569280508 / 1000000000000) (-13569248357 / 1000000000000)
    | 2 => orderedInterval (30921160345 / 1000000000000) (30921207608 / 1000000000000)
    | 3 => orderedInterval (66498507432 / 1000000000000) (66498579823 / 1000000000000)
    | _ => orderedInterval (-147952621808 / 1000000000000) (-147952506648 / 1000000000000)

theorem compactCertificate440_stateChecks0 :
    compactCertificate440.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (623 / 2)) (orderedInterval (-43141753448 / 1000000000000) (-43141753446 / 1000000000000), orderedInterval (-13440382891 / 1000000000000) (-13440382889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (917797960542323 / 4000000000000)) (orderedInterval (-41197984794 / 1000000000000) (-41197984793 / 1000000000000), orderedInterval (-32732131754 / 1000000000000) (-32732131753 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (296797003090259 / 800000000000)) (orderedInterval (36404465948 / 1000000000000) (36404465949 / 1000000000000), orderedInterval (19716755873 / 1000000000000) (19716755874 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks1 :
    compactCertificate440.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (267811155865561 / 4000000000000)) (orderedInterval (-95716866709 / 1000000000000) (-95716866329 / 1000000000000), orderedInterval (19329909337 / 1000000000000) (19329909717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (719378435410117 / 4000000000000)) (orderedInterval (-59491900260 / 1000000000000) (-59491900210 / 1000000000000), orderedInterval (-564346434 / 1000000000000) (-564346384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1953252391173489 / 4000000000000)) (orderedInterval (-30190621977 / 1000000000000) (-30190543218 / 1000000000000), orderedInterval (19835938973 / 1000000000000) (19836017732 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks2 :
    compactCertificate440.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1438756870820857 / 4000000000000)) (orderedInterval (30438691999 / 1000000000000) (30438720167 / 1000000000000), orderedInterval (-29083697704 / 1000000000000) (-29083669536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2465334420976861 / 4000000000000)) (orderedInterval (31471531358 / 1000000000000) (31471531433 / 1000000000000), orderedInterval (6490346557 / 1000000000000) (6490346632 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1815954176264599 / 4000000000000)) (orderedInterval (25723808490 / 1000000000000) (25723819394 / 1000000000000), orderedInterval (-27241697172 / 1000000000000) (-27241686268 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks3 :
    compactCertificate440.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2786140699964377 / 4000000000000)) (orderedInterval (-3414231823 / 1000000000000) (-3414231822 / 1000000000000), orderedInterval (30041159971 / 1000000000000) (30041159972 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1608579083124433 / 4000000000000)) (orderedInterval (28707703528 / 1000000000000) (28707703529 / 1000000000000), orderedInterval (27512970666 / 1000000000000) (27512970667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2854451810870597 / 4000000000000)) (orderedInterval (-28406377839 / 1000000000000) (-28406377808 / 1000000000000), orderedInterval (-9209693197 / 1000000000000) (-9209693166 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks4 :
    compactCertificate440.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2666999151465593 / 4000000000000)) (orderedInterval (30855892457 / 1000000000000) (30855893230 / 1000000000000), orderedInterval (1627381819 / 1000000000000) (1627382592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1903296438637769 / 4000000000000)) (orderedInterval (-28941873240 / 1000000000000) (-28941830833 / 1000000000000), orderedInterval (22397774608 / 1000000000000) (22397817015 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2158135306230351 / 4000000000000)) (orderedInterval (-1200071506 / 1000000000000) (-1200071505 / 1000000000000), orderedInterval (34330464959 / 1000000000000) (34330464960 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks5 :
    compactCertificate440.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1799228221418719 / 4000000000000)) (orderedInterval (-36660895410 / 1000000000000) (-36660895394 / 1000000000000), orderedInterval (-8402909021 / 1000000000000) (-8402909006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1589672698741099 / 4000000000000)) (orderedInterval (28119537061 / 1000000000000) (28119554859 / 1000000000000), orderedInterval (-28516609357 / 1000000000000) (-28516591560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (460749108564801 / 800000000000)) (orderedInterval (-32299505112 / 1000000000000) (-32299493663 / 1000000000000), orderedInterval (7908815293 / 1000000000000) (7908826742 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks6 :
    compactCertificate440.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1274456282187347 / 4000000000000)) (orderedInterval (-38625608582 / 1000000000000) (-38625558752 / 1000000000000), orderedInterval (22558446582 / 1000000000000) (22558496413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1080370704627067 / 4000000000000)) (orderedInterval (31300221608 / 1000000000000) (31300221609 / 1000000000000), orderedInterval (37054571778 / 1000000000000) (37054571779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (676045823735401 / 4000000000000)) (orderedInterval (9178293750 / 1000000000000) (9178293752 / 1000000000000), orderedInterval (60656455009 / 1000000000000) (60656455010 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks7 :
    compactCertificate440.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (363579692431767 / 4000000000000)) (orderedInterval (-45355353158 / 1000000000000) (-45355353157 / 1000000000000), orderedInterval (-70084323143 / 1000000000000) (-70084323142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (987189591276301 / 4000000000000)) (orderedInterval (28825398034 / 1000000000000) (28825404691 / 1000000000000), orderedInterval (-41874929216 / 1000000000000) (-41874922559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1347922989453677 / 4000000000000)) (orderedInterval (-43421606442 / 1000000000000) (-43421606117 / 1000000000000), orderedInterval (2000765904 / 1000000000000) (2000766229 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_stateChecks8 :
    compactCertificate440.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (569954176264599 / 4000000000000)) (orderedInterval (-63222273009 / 1000000000000) (-63222269975 / 1000000000000), orderedInterval (21919519369 / 1000000000000) (21919522403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2316832083605879 / 4000000000000)) (orderedInterval (30917100821 / 1000000000000) (30917140343 / 1000000000000), orderedInterval (-11995519864 / 1000000000000) (-11995480342 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1547536460435161 / 4000000000000)) (orderedInterval (-38537301336 / 1000000000000) (-38537301333 / 1000000000000), orderedInterval (-12614332461 / 1000000000000) (-12614332459 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_states : ∀ j,
    BesselStateValid (compactCertificate440.point j) (compactCertificate440.state j) :=
  compactCertificate440.statesValid_of_checks3 compactCertificate440_stateChecks0
    compactCertificate440_stateChecks1 compactCertificate440_stateChecks2
    compactCertificate440_stateChecks3 compactCertificate440_stateChecks4
    compactCertificate440_stateChecks5 compactCertificate440_stateChecks6
    compactCertificate440_stateChecks7 compactCertificate440_stateChecks8

theorem compactCertificate440_chunkChecks0_0 :
    compactCertificate440.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (623 / 2) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43141753448 / 1000000000000) (-43141753446 / 1000000000000), orderedInterval (-13440382891 / 1000000000000) (-13440382889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (917797960542323 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41197984794 / 1000000000000) (-41197984793 / 1000000000000), orderedInterval (-32732131754 / 1000000000000) (-32732131753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (296797003090259 / 800000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36404465948 / 1000000000000) (36404465949 / 1000000000000), orderedInterval (19716755873 / 1000000000000) (19716755874 / 1000000000000)))) (orderedInterval (-15347510546 / 1000000000000) (-15347510523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (267811155865561 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95716866709 / 1000000000000) (-95716866329 / 1000000000000), orderedInterval (19329909337 / 1000000000000) (19329909717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (719378435410117 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59491900260 / 1000000000000) (-59491900210 / 1000000000000), orderedInterval (-564346434 / 1000000000000) (-564346384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1953252391173489 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30190621977 / 1000000000000) (-30190543218 / 1000000000000), orderedInterval (19835938973 / 1000000000000) (19836017732 / 1000000000000)))) (orderedInterval (1012541845 / 1000000000000) (1012547488 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1438756870820857 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30438691999 / 1000000000000) (30438720167 / 1000000000000), orderedInterval (-29083697704 / 1000000000000) (-29083669536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2465334420976861 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31471531358 / 1000000000000) (31471531433 / 1000000000000), orderedInterval (6490346557 / 1000000000000) (6490346632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1815954176264599 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25723808490 / 1000000000000) (25723819394 / 1000000000000), orderedInterval (-27241697172 / 1000000000000) (-27241686268 / 1000000000000)))) (orderedInterval (-349014258 / 1000000000000) (-349013974 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks0_1 :
    compactCertificate440.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2786140699964377 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3414231823 / 1000000000000) (-3414231822 / 1000000000000), orderedInterval (30041159971 / 1000000000000) (30041159972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1608579083124433 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28707703528 / 1000000000000) (28707703529 / 1000000000000), orderedInterval (27512970666 / 1000000000000) (27512970667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2854451810870597 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28406377839 / 1000000000000) (-28406377808 / 1000000000000), orderedInterval (-9209693197 / 1000000000000) (-9209693166 / 1000000000000)))) (orderedInterval (-1304461675 / 1000000000000) (-1304461547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2666999151465593 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30855892457 / 1000000000000) (30855893230 / 1000000000000), orderedInterval (1627381819 / 1000000000000) (1627382592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1903296438637769 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28941873240 / 1000000000000) (-28941830833 / 1000000000000), orderedInterval (22397774608 / 1000000000000) (22397817015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2158135306230351 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1200071506 / 1000000000000) (-1200071505 / 1000000000000), orderedInterval (34330464959 / 1000000000000) (34330464960 / 1000000000000)))) (orderedInterval (-3287797541 / 1000000000000) (-3287793479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1799228221418719 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36660895410 / 1000000000000) (-36660895394 / 1000000000000), orderedInterval (-8402909021 / 1000000000000) (-8402909006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1589672698741099 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28119537061 / 1000000000000) (28119554859 / 1000000000000), orderedInterval (-28516609357 / 1000000000000) (-28516591560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (460749108564801 / 800000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32299505112 / 1000000000000) (-32299493663 / 1000000000000), orderedInterval (7908815293 / 1000000000000) (7908826742 / 1000000000000)))) (orderedInterval (-2859531535 / 1000000000000) (-2859530192 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks0_2 :
    compactCertificate440.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1274456282187347 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38625608582 / 1000000000000) (-38625558752 / 1000000000000), orderedInterval (22558446582 / 1000000000000) (22558496413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1080370704627067 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31300221608 / 1000000000000) (31300221609 / 1000000000000), orderedInterval (37054571778 / 1000000000000) (37054571779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (676045823735401 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (9178293750 / 1000000000000) (9178293752 / 1000000000000), orderedInterval (60656455009 / 1000000000000) (60656455010 / 1000000000000)))) (orderedInterval (4703145548 / 1000000000000) (4703153594 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (363579692431767 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45355353158 / 1000000000000) (-45355353157 / 1000000000000), orderedInterval (-70084323143 / 1000000000000) (-70084323142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (987189591276301 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28825398034 / 1000000000000) (28825404691 / 1000000000000), orderedInterval (-41874929216 / 1000000000000) (-41874922559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1347922989453677 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43421606442 / 1000000000000) (-43421606117 / 1000000000000), orderedInterval (2000765904 / 1000000000000) (2000766229 / 1000000000000)))) (orderedInterval (3511316732 / 1000000000000) (3511316945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (569954176264599 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63222273009 / 1000000000000) (-63222269975 / 1000000000000), orderedInterval (21919519369 / 1000000000000) (21919522403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2316832083605879 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30917100821 / 1000000000000) (30917140343 / 1000000000000), orderedInterval (-11995519864 / 1000000000000) (-11995480342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1547536460435161 / 4000000000000) 0 (IntervalRat.scale (623 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38537301336 / 1000000000000) (-38537301333 / 1000000000000), orderedInterval (-12614332461 / 1000000000000) (-12614332459 / 1000000000000)))) (orderedInterval (4332785203 / 1000000000000) (4332788526 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks0 :
    compactCertificate440.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate440.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate440_chunkChecks0_0
    compactCertificate440_chunkChecks0_1 compactCertificate440_chunkChecks0_2

theorem compactCertificate440_chunkChecks1_0 :
    compactCertificate440.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (623 / 2) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43141753448 / 1000000000000) (-43141753446 / 1000000000000), orderedInterval (-13440382891 / 1000000000000) (-13440382889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (917797960542323 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41197984794 / 1000000000000) (-41197984793 / 1000000000000), orderedInterval (-32732131754 / 1000000000000) (-32732131753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (296797003090259 / 800000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36404465948 / 1000000000000) (36404465949 / 1000000000000), orderedInterval (19716755873 / 1000000000000) (19716755874 / 1000000000000)))) (orderedInterval (-4173970754 / 1000000000000) (-4173970728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (267811155865561 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95716866709 / 1000000000000) (-95716866329 / 1000000000000), orderedInterval (19329909337 / 1000000000000) (19329909717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (719378435410117 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59491900260 / 1000000000000) (-59491900210 / 1000000000000), orderedInterval (-564346434 / 1000000000000) (-564346384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1953252391173489 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30190621977 / 1000000000000) (-30190543218 / 1000000000000), orderedInterval (19835938973 / 1000000000000) (19836017732 / 1000000000000)))) (orderedInterval (-2267526126 / 1000000000000) (-2267517304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1438756870820857 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30438691999 / 1000000000000) (30438720167 / 1000000000000), orderedInterval (-29083697704 / 1000000000000) (-29083669536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2465334420976861 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31471531358 / 1000000000000) (31471531433 / 1000000000000), orderedInterval (6490346557 / 1000000000000) (6490346632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1815954176264599 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25723808490 / 1000000000000) (25723819394 / 1000000000000), orderedInterval (-27241697172 / 1000000000000) (-27241686268 / 1000000000000)))) (orderedInterval (-1355630364 / 1000000000000) (-1355629944 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks1_1 :
    compactCertificate440.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2786140699964377 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3414231823 / 1000000000000) (-3414231822 / 1000000000000), orderedInterval (30041159971 / 1000000000000) (30041159972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1608579083124433 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28707703528 / 1000000000000) (28707703529 / 1000000000000), orderedInterval (27512970666 / 1000000000000) (27512970667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2854451810870597 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28406377839 / 1000000000000) (-28406377808 / 1000000000000), orderedInterval (-9209693197 / 1000000000000) (-9209693166 / 1000000000000)))) (orderedInterval (-12303613924 / 1000000000000) (-12303613657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2666999151465593 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30855892457 / 1000000000000) (30855893230 / 1000000000000), orderedInterval (1627381819 / 1000000000000) (1627382592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1903296438637769 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28941873240 / 1000000000000) (-28941830833 / 1000000000000), orderedInterval (22397774608 / 1000000000000) (22397817015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2158135306230351 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1200071506 / 1000000000000) (-1200071505 / 1000000000000), orderedInterval (34330464959 / 1000000000000) (34330464960 / 1000000000000)))) (orderedInterval (2871497624 / 1000000000000) (2871503840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1799228221418719 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36660895410 / 1000000000000) (-36660895394 / 1000000000000), orderedInterval (-8402909021 / 1000000000000) (-8402909006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1589672698741099 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28119537061 / 1000000000000) (28119554859 / 1000000000000), orderedInterval (-28516609357 / 1000000000000) (-28516591560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (460749108564801 / 800000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32299505112 / 1000000000000) (-32299493663 / 1000000000000), orderedInterval (7908815293 / 1000000000000) (7908826742 / 1000000000000)))) (orderedInterval (2316306097 / 1000000000000) (2316307982 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks1_2 :
    compactCertificate440.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1274456282187347 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38625608582 / 1000000000000) (-38625558752 / 1000000000000), orderedInterval (22558446582 / 1000000000000) (22558496413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1080370704627067 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31300221608 / 1000000000000) (31300221609 / 1000000000000), orderedInterval (37054571778 / 1000000000000) (37054571779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (676045823735401 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (9178293750 / 1000000000000) (9178293752 / 1000000000000), orderedInterval (60656455009 / 1000000000000) (60656455010 / 1000000000000)))) (orderedInterval (-4436394078 / 1000000000000) (-4436385856 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (363579692431767 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45355353158 / 1000000000000) (-45355353157 / 1000000000000), orderedInterval (-70084323143 / 1000000000000) (-70084323142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (987189591276301 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28825398034 / 1000000000000) (28825404691 / 1000000000000), orderedInterval (-41874929216 / 1000000000000) (-41874922559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1347922989453677 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43421606442 / 1000000000000) (-43421606117 / 1000000000000), orderedInterval (2000765904 / 1000000000000) (2000766229 / 1000000000000)))) (orderedInterval (964421201 / 1000000000000) (964421382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (569954176264599 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63222273009 / 1000000000000) (-63222269975 / 1000000000000), orderedInterval (21919519369 / 1000000000000) (21919522403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2316832083605879 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30917100821 / 1000000000000) (30917140343 / 1000000000000), orderedInterval (-11995519864 / 1000000000000) (-11995480342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1547536460435161 / 4000000000000) 1 (IntervalRat.scale (623 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38537301336 / 1000000000000) (-38537301333 / 1000000000000), orderedInterval (-12614332461 / 1000000000000) (-12614332459 / 1000000000000)))) (orderedInterval (4815629816 / 1000000000000) (4815635928 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks1 :
    compactCertificate440.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate440.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate440_chunkChecks1_0
    compactCertificate440_chunkChecks1_1 compactCertificate440_chunkChecks1_2

theorem compactCertificate440_chunkChecks2_0 :
    compactCertificate440.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (623 / 2) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43141753448 / 1000000000000) (-43141753446 / 1000000000000), orderedInterval (-13440382891 / 1000000000000) (-13440382889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (917797960542323 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41197984794 / 1000000000000) (-41197984793 / 1000000000000), orderedInterval (-32732131754 / 1000000000000) (-32732131753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (296797003090259 / 800000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36404465948 / 1000000000000) (36404465949 / 1000000000000), orderedInterval (19716755873 / 1000000000000) (19716755874 / 1000000000000)))) (orderedInterval (14291332221 / 1000000000000) (14291332251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (267811155865561 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95716866709 / 1000000000000) (-95716866329 / 1000000000000), orderedInterval (19329909337 / 1000000000000) (19329909717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (719378435410117 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59491900260 / 1000000000000) (-59491900210 / 1000000000000), orderedInterval (-564346434 / 1000000000000) (-564346384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1953252391173489 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30190621977 / 1000000000000) (-30190543218 / 1000000000000), orderedInterval (19835938973 / 1000000000000) (19836017732 / 1000000000000)))) (orderedInterval (-4590873729 / 1000000000000) (-4590859882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1438756870820857 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30438691999 / 1000000000000) (30438720167 / 1000000000000), orderedInterval (-29083697704 / 1000000000000) (-29083669536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2465334420976861 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31471531358 / 1000000000000) (31471531433 / 1000000000000), orderedInterval (6490346557 / 1000000000000) (6490346632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1815954176264599 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25723808490 / 1000000000000) (25723819394 / 1000000000000), orderedInterval (-27241697172 / 1000000000000) (-27241686268 / 1000000000000)))) (orderedInterval (2483995730 / 1000000000000) (2483996355 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks2_1 :
    compactCertificate440.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2786140699964377 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3414231823 / 1000000000000) (-3414231822 / 1000000000000), orderedInterval (30041159971 / 1000000000000) (30041159972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1608579083124433 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28707703528 / 1000000000000) (28707703529 / 1000000000000), orderedInterval (27512970666 / 1000000000000) (27512970667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2854451810870597 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28406377839 / 1000000000000) (-28406377808 / 1000000000000), orderedInterval (-9209693197 / 1000000000000) (-9209693166 / 1000000000000)))) (orderedInterval (14654035618 / 1000000000000) (14654036191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2666999151465593 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30855892457 / 1000000000000) (30855893230 / 1000000000000), orderedInterval (1627381819 / 1000000000000) (1627382592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1903296438637769 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28941873240 / 1000000000000) (-28941830833 / 1000000000000), orderedInterval (22397774608 / 1000000000000) (22397817015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2158135306230351 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1200071506 / 1000000000000) (-1200071505 / 1000000000000), orderedInterval (34330464959 / 1000000000000) (34330464960 / 1000000000000)))) (orderedInterval (8910590664 / 1000000000000) (8910600205 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1799228221418719 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36660895410 / 1000000000000) (-36660895394 / 1000000000000), orderedInterval (-8402909021 / 1000000000000) (-8402909006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1589672698741099 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28119537061 / 1000000000000) (28119554859 / 1000000000000), orderedInterval (-28516609357 / 1000000000000) (-28516591560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (460749108564801 / 800000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32299505112 / 1000000000000) (-32299493663 / 1000000000000), orderedInterval (7908815293 / 1000000000000) (7908826742 / 1000000000000)))) (orderedInterval (6321674780 / 1000000000000) (6321677511 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks2_2 :
    compactCertificate440.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1274456282187347 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38625608582 / 1000000000000) (-38625558752 / 1000000000000), orderedInterval (22558446582 / 1000000000000) (22558496413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1080370704627067 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31300221608 / 1000000000000) (31300221609 / 1000000000000), orderedInterval (37054571778 / 1000000000000) (37054571779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (676045823735401 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (9178293750 / 1000000000000) (9178293752 / 1000000000000), orderedInterval (60656455009 / 1000000000000) (60656455010 / 1000000000000)))) (orderedInterval (-5203074431 / 1000000000000) (-5203066000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (363579692431767 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45355353158 / 1000000000000) (-45355353157 / 1000000000000), orderedInterval (-70084323143 / 1000000000000) (-70084323142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (987189591276301 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28825398034 / 1000000000000) (28825404691 / 1000000000000), orderedInterval (-41874929216 / 1000000000000) (-41874922559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1347922989453677 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43421606442 / 1000000000000) (-43421606117 / 1000000000000), orderedInterval (2000765904 / 1000000000000) (2000766229 / 1000000000000)))) (orderedInterval (-3558379650 / 1000000000000) (-3558379492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (569954176264599 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63222273009 / 1000000000000) (-63222269975 / 1000000000000), orderedInterval (21919519369 / 1000000000000) (21919522403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2316832083605879 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30917100821 / 1000000000000) (30917140343 / 1000000000000), orderedInterval (-11995519864 / 1000000000000) (-11995480342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1547536460435161 / 4000000000000) 2 (IntervalRat.scale (623 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38537301336 / 1000000000000) (-38537301333 / 1000000000000), orderedInterval (-12614332461 / 1000000000000) (-12614332459 / 1000000000000)))) (orderedInterval (-2388140858 / 1000000000000) (-2388129531 / 1000000000000))) = true
  rfl'

theorem compactCertificate440_chunkChecks2 :
    compactCertificate440.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate440.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate440_chunkChecks2_0
    compactCertificate440_chunkChecks2_1 compactCertificate440_chunkChecks2_2

theorem compactCertificate440_chunkChecks3_0 :
    compactCertificate440.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (623 / 2) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43141753448 / 1000000000000) (-43141753446 / 1000000000000), orderedInterval (-13440382891 / 1000000000000) (-13440382889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (917797960542323 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41197984794 / 1000000000000) (-41197984793 / 1000000000000), orderedInterval (-32732131754 / 1000000000000) (-32732131753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (296797003090259 / 800000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36404465948 / 1000000000000) (36404465949 / 1000000000000), orderedInterval (19716755873 / 1000000000000) (19716755874 / 1000000000000)))) (orderedInterval (3448623073 / 1000000000000) (3448623107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (267811155865561 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95716866709 / 1000000000000) (-95716866329 / 1000000000000), orderedInterval (19329909337 / 1000000000000) (19329909717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (719378435410117 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59491900260 / 1000000000000) (-59491900210 / 1000000000000), orderedInterval (-564346434 / 1000000000000) (-564346384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1953252391173489 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30190621977 / 1000000000000) (-30190543218 / 1000000000000), orderedInterval (19835938973 / 1000000000000) (19836017732 / 1000000000000)))) (orderedInterval (5453016170 / 1000000000000) (5453037872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1438756870820857 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30438691999 / 1000000000000) (30438720167 / 1000000000000), orderedInterval (-29083697704 / 1000000000000) (-29083669536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2465334420976861 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31471531358 / 1000000000000) (31471531433 / 1000000000000), orderedInterval (6490346557 / 1000000000000) (6490346632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1815954176264599 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25723808490 / 1000000000000) (25723819394 / 1000000000000), orderedInterval (-27241697172 / 1000000000000) (-27241686268 / 1000000000000)))) (orderedInterval (3580803241 / 1000000000000) (3580804175 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate440_chunkChecks3_1 :
    compactCertificate440.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2786140699964377 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3414231823 / 1000000000000) (-3414231822 / 1000000000000), orderedInterval (30041159971 / 1000000000000) (30041159972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1608579083124433 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28707703528 / 1000000000000) (28707703529 / 1000000000000), orderedInterval (27512970666 / 1000000000000) (27512970667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2854451810870597 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28406377839 / 1000000000000) (-28406377808 / 1000000000000), orderedInterval (-9209693197 / 1000000000000) (-9209693166 / 1000000000000)))) (orderedInterval (70987519593 / 1000000000000) (70987520850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2666999151465593 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30855892457 / 1000000000000) (30855893230 / 1000000000000), orderedInterval (1627381819 / 1000000000000) (1627382592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1903296438637769 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28941873240 / 1000000000000) (-28941830833 / 1000000000000), orderedInterval (22397774608 / 1000000000000) (22397817015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2158135306230351 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1200071506 / 1000000000000) (-1200071505 / 1000000000000), orderedInterval (34330464959 / 1000000000000) (34330464960 / 1000000000000)))) (orderedInterval (-6386766310 / 1000000000000) (-6386751681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1799228221418719 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36660895410 / 1000000000000) (-36660895394 / 1000000000000), orderedInterval (-8402909021 / 1000000000000) (-8402909006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1589672698741099 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28119537061 / 1000000000000) (28119554859 / 1000000000000), orderedInterval (-28516609357 / 1000000000000) (-28516591560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (460749108564801 / 800000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32299505112 / 1000000000000) (-32299493663 / 1000000000000), orderedInterval (7908815293 / 1000000000000) (7908826742 / 1000000000000)))) (orderedInterval (-4396934875 / 1000000000000) (-4396930799 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate440_chunkChecks3_2 :
    compactCertificate440.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1274456282187347 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38625608582 / 1000000000000) (-38625558752 / 1000000000000), orderedInterval (22558446582 / 1000000000000) (22558496413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1080370704627067 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31300221608 / 1000000000000) (31300221609 / 1000000000000), orderedInterval (37054571778 / 1000000000000) (37054571779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (676045823735401 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (9178293750 / 1000000000000) (9178293752 / 1000000000000), orderedInterval (60656455009 / 1000000000000) (60656455010 / 1000000000000)))) (orderedInterval (4928156449 / 1000000000000) (4928165069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (363579692431767 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45355353158 / 1000000000000) (-45355353157 / 1000000000000), orderedInterval (-70084323143 / 1000000000000) (-70084323142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (987189591276301 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28825398034 / 1000000000000) (28825404691 / 1000000000000), orderedInterval (-41874929216 / 1000000000000) (-41874922559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1347922989453677 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43421606442 / 1000000000000) (-43421606117 / 1000000000000), orderedInterval (2000765904 / 1000000000000) (2000766229 / 1000000000000)))) (orderedInterval (-299064200 / 1000000000000) (-299064058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (569954176264599 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63222273009 / 1000000000000) (-63222269975 / 1000000000000), orderedInterval (21919519369 / 1000000000000) (21919522403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2316832083605879 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30917100821 / 1000000000000) (30917140343 / 1000000000000), orderedInterval (-11995519864 / 1000000000000) (-11995480342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1547536460435161 / 4000000000000) 3 (IntervalRat.scale (623 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38537301336 / 1000000000000) (-38537301333 / 1000000000000), orderedInterval (-12614332461 / 1000000000000) (-12614332459 / 1000000000000)))) (orderedInterval (-10816845709 / 1000000000000) (-10816824712 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate440_chunkChecks3 :
    compactCertificate440.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate440.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate440_chunkChecks3_0
    compactCertificate440_chunkChecks3_1 compactCertificate440_chunkChecks3_2

theorem compactCertificate440_chunkChecks4_0 :
    compactCertificate440.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (623 / 2) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43141753448 / 1000000000000) (-43141753446 / 1000000000000), orderedInterval (-13440382891 / 1000000000000) (-13440382889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (917797960542323 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41197984794 / 1000000000000) (-41197984793 / 1000000000000), orderedInterval (-32732131754 / 1000000000000) (-32732131753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (296797003090259 / 800000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36404465948 / 1000000000000) (36404465949 / 1000000000000), orderedInterval (19716755873 / 1000000000000) (19716755874 / 1000000000000)))) (orderedInterval (-12936562129 / 1000000000000) (-12936562089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (267811155865561 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-95716866709 / 1000000000000) (-95716866329 / 1000000000000), orderedInterval (19329909337 / 1000000000000) (19329909717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (719378435410117 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59491900260 / 1000000000000) (-59491900210 / 1000000000000), orderedInterval (-564346434 / 1000000000000) (-564346384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1953252391173489 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30190621977 / 1000000000000) (-30190543218 / 1000000000000), orderedInterval (19835938973 / 1000000000000) (19836017732 / 1000000000000)))) (orderedInterval (12686807993 / 1000000000000) (12686842079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1438756870820857 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30438691999 / 1000000000000) (30438720167 / 1000000000000), orderedInterval (-29083697704 / 1000000000000) (-29083669536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2465334420976861 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31471531358 / 1000000000000) (31471531433 / 1000000000000), orderedInterval (6490346557 / 1000000000000) (6490346632 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1815954176264599 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25723808490 / 1000000000000) (25723819394 / 1000000000000), orderedInterval (-27241697172 / 1000000000000) (-27241686268 / 1000000000000)))) (orderedInterval (-12095174552 / 1000000000000) (-12095173140 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate440_chunkChecks4_1 :
    compactCertificate440.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2786140699964377 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3414231823 / 1000000000000) (-3414231822 / 1000000000000), orderedInterval (30041159971 / 1000000000000) (30041159972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1608579083124433 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28707703528 / 1000000000000) (28707703529 / 1000000000000), orderedInterval (27512970666 / 1000000000000) (27512970667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2854451810870597 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28406377839 / 1000000000000) (-28406377808 / 1000000000000), orderedInterval (-9209693197 / 1000000000000) (-9209693166 / 1000000000000)))) (orderedInterval (-90604820572 / 1000000000000) (-90604817776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2666999151465593 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30855892457 / 1000000000000) (30855893230 / 1000000000000), orderedInterval (1627381819 / 1000000000000) (1627382592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1903296438637769 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28941873240 / 1000000000000) (-28941830833 / 1000000000000), orderedInterval (22397774608 / 1000000000000) (22397817015 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2158135306230351 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1200071506 / 1000000000000) (-1200071505 / 1000000000000), orderedInterval (34330464959 / 1000000000000) (34330464960 / 1000000000000)))) (orderedInterval (-26497285592 / 1000000000000) (-26497263080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1799228221418719 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36660895410 / 1000000000000) (-36660895394 / 1000000000000), orderedInterval (-8402909021 / 1000000000000) (-8402909006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1589672698741099 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28119537061 / 1000000000000) (28119554859 / 1000000000000), orderedInterval (-28516609357 / 1000000000000) (-28516591560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (460749108564801 / 800000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32299505112 / 1000000000000) (-32299493663 / 1000000000000), orderedInterval (7908815293 / 1000000000000) (7908826742 / 1000000000000)))) (orderedInterval (-15740106552 / 1000000000000) (-15740100245 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate440_chunkChecks4_2 :
    compactCertificate440.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1274456282187347 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38625608582 / 1000000000000) (-38625558752 / 1000000000000), orderedInterval (22558446582 / 1000000000000) (22558496413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1080370704627067 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (31300221608 / 1000000000000) (31300221609 / 1000000000000), orderedInterval (37054571778 / 1000000000000) (37054571779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (676045823735401 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (9178293750 / 1000000000000) (9178293752 / 1000000000000), orderedInterval (60656455009 / 1000000000000) (60656455010 / 1000000000000)))) (orderedInterval (5752602693 / 1000000000000) (5752611534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (363579692431767 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45355353158 / 1000000000000) (-45355353157 / 1000000000000), orderedInterval (-70084323143 / 1000000000000) (-70084323142 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (987189591276301 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (28825398034 / 1000000000000) (28825404691 / 1000000000000), orderedInterval (-41874929216 / 1000000000000) (-41874922559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1347922989453677 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43421606442 / 1000000000000) (-43421606117 / 1000000000000), orderedInterval (2000765904 / 1000000000000) (2000766229 / 1000000000000)))) (orderedInterval (4307948186 / 1000000000000) (4307948317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (569954176264599 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63222273009 / 1000000000000) (-63222269975 / 1000000000000), orderedInterval (21919519369 / 1000000000000) (21919522403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2316832083605879 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30917100821 / 1000000000000) (30917140343 / 1000000000000), orderedInterval (-11995519864 / 1000000000000) (-11995480342 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1547536460435161 / 4000000000000) 4 (IntervalRat.scale (623 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38537301336 / 1000000000000) (-38537301333 / 1000000000000), orderedInterval (-12614332461 / 1000000000000) (-12614332459 / 1000000000000)))) (orderedInterval (-12826031283 / 1000000000000) (-12825992248 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate440_chunkChecks4 :
    compactCertificate440.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate440.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate440_chunkChecks4_0
    compactCertificate440_chunkChecks4_1 compactCertificate440_chunkChecks4_2

theorem compactCertificate440_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate440.chunkCheck r b = true :=
  compactCertificate440.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate440_chunkChecks0
    · exact compactCertificate440_chunkChecks1
    · exact compactCertificate440_chunkChecks2
    · exact compactCertificate440_chunkChecks3
    · exact compactCertificate440_chunkChecks4)

theorem compactCertificate440_coefficient0 :
    compactCertificate440.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate440_coefficient1 :
    compactCertificate440.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate440_coefficient2 :
    compactCertificate440.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate440_coefficient3 :
    compactCertificate440.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate440_coefficient4 :
    compactCertificate440.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate440_coefficients : ∀ r : Fin 5,
    compactCertificate440.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate440_coefficient0
  · exact compactCertificate440_coefficient1
  · exact compactCertificate440_coefficient2
  · exact compactCertificate440_coefficient3
  · exact compactCertificate440_coefficient4

theorem compactCertificate440_lower : (1 : ℚ) ≤ compactCertificate440.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate440, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate440_proves {t : ℝ} (ht : t ∈ compactCertificate440.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate440.proves compactCertificate440_states compactCertificate440_chunks
    compactCertificate440_coefficients compactCertificate440_lower ht

end Erdos232
