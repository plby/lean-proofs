/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate503 : CompactCertificate where
  left := 374
  right := 375
  center := 749 / 2
  grid := fun i =>
    match i.val with
    | 0 => 119
    | 1 => 88
    | 2 => 142
    | 3 => 26
    | 4 => 69
    | 5 => 187
    | 6 => 138
    | 7 => 236
    | 8 => 174
    | 9 => 267
    | 10 => 154
    | 11 => 273
    | 12 => 255
    | 13 => 182
    | 14 => 207
    | 15 => 172
    | 16 => 152
    | 17 => 221
    | 18 => 122
    | 19 => 103
    | 20 => 65
    | 21 => 35
    | 22 => 94
    | 23 => 129
    | 24 => 55
    | 25 => 222
    | _ => 148
  point := fun i =>
    match i.val with
    | 0 => 749 / 2
    | 1 => 1103420019977849 / 4000000000000
    | 2 => 356823363265817 / 800000000000
    | 3 => 321975209860843 / 4000000000000
    | 4 => 864870703245871 / 4000000000000
    | 5 => 2348292200624307 / 4000000000000
    | 6 => 1729741406492491 / 4000000000000
    | 7 => 2963941382522743 / 4000000000000
    | 8 => 2183225807419237 / 4000000000000
    | 9 => 3349629830294251 / 4000000000000
    | 10 => 1933909684205779 / 4000000000000
    | 11 => 3431756671496111 / 4000000000000
    | 12 => 3206392238278859 / 4000000000000
    | 13 => 2288232797013947 / 4000000000000
    | 14 => 2594612109737613 / 4000000000000
    | 15 => 2163117075188797 / 4000000000000
    | 16 => 1911179536688737 / 4000000000000
    | 17 => 553934321532963 / 800000000000
    | 18 => 1532211485326361 / 4000000000000
    | 19 => 1298872644888721 / 4000000000000
    | 20 => 812774192580763 / 4000000000000
    | 21 => 437112663934821 / 4000000000000
    | 22 => 1186845913107463 / 4000000000000
    | 23 => 1620536627770151 / 4000000000000
    | 24 => 685225807419237 / 4000000000000
    | 25 => 2785404864559877 / 4000000000000
    | _ => 1860521362545643 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-40853488952 / 1000000000000) (-40853488918 / 1000000000000), orderedInterval (-5505156350 / 1000000000000) (-5505156316 / 1000000000000))
    | 1 => (orderedInterval (8590888991 / 1000000000000) (8590888992 / 1000000000000), orderedInterval (47249700751 / 1000000000000) (47249700752 / 1000000000000))
    | 2 => (orderedInterval (24573461339 / 1000000000000) (24573461340 / 1000000000000), orderedInterval (28668276305 / 1000000000000) (28668276306 / 1000000000000))
    | 3 => (orderedInterval (-34939315981 / 1000000000000) (-34939314087 / 1000000000000), orderedInterval (81998919226 / 1000000000000) (81998921120 / 1000000000000))
    | 4 => (orderedInterval (-12507931192 / 1000000000000) (-12507931191 / 1000000000000), orderedInterval (-52771693786 / 1000000000000) (-52771693785 / 1000000000000))
    | 5 => (orderedInterval (-12226984442 / 1000000000000) (-12226984441 / 1000000000000), orderedInterval (-30565677078 / 1000000000000) (-30565677077 / 1000000000000))
    | 6 => (orderedInterval (-12045002248 / 1000000000000) (-12045002182 / 1000000000000), orderedInterval (36443200792 / 1000000000000) (36443200858 / 1000000000000))
    | 7 => (orderedInterval (10180326116 / 1000000000000) (10180326117 / 1000000000000), orderedInterval (27479747198 / 1000000000000) (27479747199 / 1000000000000))
    | 8 => (orderedInterval (-1553420704 / 1000000000000) (-1553420703 / 1000000000000), orderedInterval (34118443943 / 1000000000000) (34118443944 / 1000000000000))
    | 9 => (orderedInterval (15852395204 / 1000000000000) (15852395428 / 1000000000000), orderedInterval (-22568911723 / 1000000000000) (-22568911498 / 1000000000000))
    | 10 => (orderedInterval (16021464697 / 1000000000000) (16021464698 / 1000000000000), orderedInterval (32542069128 / 1000000000000) (32542069129 / 1000000000000))
    | 11 => (orderedInterval (-23890304591 / 1000000000000) (-23890304585 / 1000000000000), orderedInterval (-13073741951 / 1000000000000) (-13073741945 / 1000000000000))
    | 12 => (orderedInterval (-26975241193 / 1000000000000) (-26975241113 / 1000000000000), orderedInterval (-8139429483 / 1000000000000) (-8139429403 / 1000000000000))
    | 13 => (orderedInterval (29319126090 / 1000000000000) (29319126091 / 1000000000000), orderedInterval (15888110657 / 1000000000000) (15888110658 / 1000000000000))
    | 14 => (orderedInterval (23974145137 / 1000000000000) (23974157842 / 1000000000000), orderedInterval (-20185014394 / 1000000000000) (-20185001689 / 1000000000000))
    | 15 => (orderedInterval (32107712368 / 1000000000000) (32107712372 / 1000000000000), orderedInterval (12066638901 / 1000000000000) (12066638905 / 1000000000000))
    | 16 => (orderedInterval (31806030493 / 1000000000000) (31806030494 / 1000000000000), orderedInterval (17877280574 / 1000000000000) (17877280575 / 1000000000000))
    | 17 => (orderedInterval (26868091844 / 1000000000000) (26868167442 / 1000000000000), orderedInterval (-14073582429 / 1000000000000) (-14073506831 / 1000000000000))
    | 18 => (orderedInterval (21780518586 / 1000000000000) (21780518587 / 1000000000000), orderedInterval (34432748159 / 1000000000000) (34432748160 / 1000000000000))
    | 19 => (orderedInterval (-41618632529 / 1000000000000) (-41618622978 / 1000000000000), orderedInterval (15177591712 / 1000000000000) (15177601263 / 1000000000000))
    | 20 => (orderedInterval (12498540989 / 1000000000000) (12498541080 / 1000000000000), orderedInterval (-54591416871 / 1000000000000) (-54591416780 / 1000000000000))
    | 21 => (orderedInterval (-8126802240 / 1000000000000) (-8126802239 / 1000000000000), orderedInterval (-75855477901 / 1000000000000) (-75855477899 / 1000000000000))
    | 22 => (orderedInterval (37807857386 / 1000000000000) (37807954314 / 1000000000000), orderedInterval (-26824669610 / 1000000000000) (-26824572682 / 1000000000000))
    | 23 => (orderedInterval (-24109529143 / 1000000000000) (-24109529142 / 1000000000000), orderedInterval (-31436275403 / 1000000000000) (-31436275402 / 1000000000000))
    | 24 => (orderedInterval (39107588814 / 1000000000000) (39107612822 / 1000000000000), orderedInterval (-46878041219 / 1000000000000) (-46878017211 / 1000000000000))
    | 25 => (orderedInterval (-8852565646 / 1000000000000) (-8852565639 / 1000000000000), orderedInterval (28917505140 / 1000000000000) (28917505146 / 1000000000000))
    | _ => (orderedInterval (30301509977 / 1000000000000) (30301509978 / 1000000000000), orderedInterval (21192632545 / 1000000000000) (21192632546 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14670843732 / 1000000000000) (-14670843692 / 1000000000000)
      | 1 => orderedInterval (791592291 / 1000000000000) (791592357 / 1000000000000)
      | 2 => orderedInterval (-351545113 / 1000000000000) (-351545092 / 1000000000000)
      | 3 => orderedInterval (-5025868206 / 1000000000000) (-5025868017 / 1000000000000)
      | 4 => orderedInterval (3138163869 / 1000000000000) (3138163980 / 1000000000000)
      | 5 => orderedInterval (-761454905 / 1000000000000) (-761452933 / 1000000000000)
      | 6 => orderedInterval (-720034734 / 1000000000000) (-720034096 / 1000000000000)
      | 7 => orderedInterval (1140045559 / 1000000000000) (1140047803 / 1000000000000)
      | _ => orderedInterval (-4728999185 / 1000000000000) (-4728998936 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (145856351 / 1000000000000) (145856394 / 1000000000000)
      | 1 => orderedInterval (2102637481 / 1000000000000) (2102637537 / 1000000000000)
      | 2 => orderedInterval (-475272941 / 1000000000000) (-475272904 / 1000000000000)
      | 3 => orderedInterval (7822202369 / 1000000000000) (7822202768 / 1000000000000)
      | 4 => orderedInterval (2786438987 / 1000000000000) (2786439174 / 1000000000000)
      | 5 => orderedInterval (-1770264183 / 1000000000000) (-1770260552 / 1000000000000)
      | 6 => orderedInterval (-7340412486 / 1000000000000) (-7340411928 / 1000000000000)
      | 7 => orderedInterval (3497190296 / 1000000000000) (3497192080 / 1000000000000)
      | _ => orderedInterval (-9444792479 / 1000000000000) (-9444792265 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14103625095 / 1000000000000) (14103625143 / 1000000000000)
      | 1 => orderedInterval (-2006922773 / 1000000000000) (-2006922701 / 1000000000000)
      | 2 => orderedInterval (1310286157 / 1000000000000) (1310286223 / 1000000000000)
      | 3 => orderedInterval (29908196918 / 1000000000000) (29908197781 / 1000000000000)
      | 4 => orderedInterval (-8343777710 / 1000000000000) (-8343777390 / 1000000000000)
      | 5 => orderedInterval (-157361772 / 1000000000000) (-157355068 / 1000000000000)
      | 6 => orderedInterval (1772264049 / 1000000000000) (1772264541 / 1000000000000)
      | 7 => orderedInterval (-1646074456 / 1000000000000) (-1646073030 / 1000000000000)
      | _ => orderedInterval (6254511445 / 1000000000000) (6254511693 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-873635222 / 1000000000000) (-873635168 / 1000000000000)
      | 1 => orderedInterval (-7985673143 / 1000000000000) (-7985673036 / 1000000000000)
      | 2 => orderedInterval (4009183844 / 1000000000000) (4009183963 / 1000000000000)
      | 3 => orderedInterval (-27758404846 / 1000000000000) (-27758402943 / 1000000000000)
      | 4 => orderedInterval (-7304445074 / 1000000000000) (-7304444521 / 1000000000000)
      | 5 => orderedInterval (3982917599 / 1000000000000) (3982929970 / 1000000000000)
      | 6 => orderedInterval (6730503961 / 1000000000000) (6730504396 / 1000000000000)
      | 7 => orderedInterval (-3383191667 / 1000000000000) (-3383190528 / 1000000000000)
      | _ => orderedInterval (22761370199 / 1000000000000) (22761370548 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13263139917 / 1000000000000) (-13263139858 / 1000000000000)
      | 1 => orderedInterval (5241824436 / 1000000000000) (5241824600 / 1000000000000)
      | 2 => orderedInterval (-5003208388 / 1000000000000) (-5003208168 / 1000000000000)
      | 3 => orderedInterval (-160515339480 / 1000000000000) (-160515335250 / 1000000000000)
      | 4 => orderedInterval (24263773235 / 1000000000000) (24263774200 / 1000000000000)
      | 5 => orderedInterval (4807473763 / 1000000000000) (4807496637 / 1000000000000)
      | 6 => orderedInterval (-2480969186 / 1000000000000) (-2480968799 / 1000000000000)
      | 7 => orderedInterval (2211780827 / 1000000000000) (2211781743 / 1000000000000)
      | _ => orderedInterval (-5025613834 / 1000000000000) (-5025613287 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-21188944156 / 1000000000000) (-21188938626 / 1000000000000)
    | 1 => orderedInterval (-2676416605 / 1000000000000) (-2676409696 / 1000000000000)
    | 2 => orderedInterval (41194746953 / 1000000000000) (41194757192 / 1000000000000)
    | 3 => orderedInterval (-9821374349 / 1000000000000) (-9821357319 / 1000000000000)
    | _ => orderedInterval (-149763418544 / 1000000000000) (-149763388182 / 1000000000000)

theorem compactCertificate503_stateChecks0 :
    compactCertificate503.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (749 / 2)) (orderedInterval (-40853488952 / 1000000000000) (-40853488918 / 1000000000000), orderedInterval (-5505156350 / 1000000000000) (-5505156316 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1103420019977849 / 4000000000000)) (orderedInterval (8590888991 / 1000000000000) (8590888992 / 1000000000000), orderedInterval (47249700751 / 1000000000000) (47249700752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (356823363265817 / 800000000000)) (orderedInterval (24573461339 / 1000000000000) (24573461340 / 1000000000000), orderedInterval (28668276305 / 1000000000000) (28668276306 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks1 :
    compactCertificate503.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (321975209860843 / 4000000000000)) (orderedInterval (-34939315981 / 1000000000000) (-34939314087 / 1000000000000), orderedInterval (81998919226 / 1000000000000) (81998921120 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (864870703245871 / 4000000000000)) (orderedInterval (-12507931192 / 1000000000000) (-12507931191 / 1000000000000), orderedInterval (-52771693786 / 1000000000000) (-52771693785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2348292200624307 / 4000000000000)) (orderedInterval (-12226984442 / 1000000000000) (-12226984441 / 1000000000000), orderedInterval (-30565677078 / 1000000000000) (-30565677077 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks2 :
    compactCertificate503.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1729741406492491 / 4000000000000)) (orderedInterval (-12045002248 / 1000000000000) (-12045002182 / 1000000000000), orderedInterval (36443200792 / 1000000000000) (36443200858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2963941382522743 / 4000000000000)) (orderedInterval (10180326116 / 1000000000000) (10180326117 / 1000000000000), orderedInterval (27479747198 / 1000000000000) (27479747199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2183225807419237 / 4000000000000)) (orderedInterval (-1553420704 / 1000000000000) (-1553420703 / 1000000000000), orderedInterval (34118443943 / 1000000000000) (34118443944 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks3 :
    compactCertificate503.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3349629830294251 / 4000000000000)) (orderedInterval (15852395204 / 1000000000000) (15852395428 / 1000000000000), orderedInterval (-22568911723 / 1000000000000) (-22568911498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1933909684205779 / 4000000000000)) (orderedInterval (16021464697 / 1000000000000) (16021464698 / 1000000000000), orderedInterval (32542069128 / 1000000000000) (32542069129 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3431756671496111 / 4000000000000)) (orderedInterval (-23890304591 / 1000000000000) (-23890304585 / 1000000000000), orderedInterval (-13073741951 / 1000000000000) (-13073741945 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks4 :
    compactCertificate503.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (3206392238278859 / 4000000000000)) (orderedInterval (-26975241193 / 1000000000000) (-26975241113 / 1000000000000), orderedInterval (-8139429483 / 1000000000000) (-8139429403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2288232797013947 / 4000000000000)) (orderedInterval (29319126090 / 1000000000000) (29319126091 / 1000000000000), orderedInterval (15888110657 / 1000000000000) (15888110658 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2594612109737613 / 4000000000000)) (orderedInterval (23974145137 / 1000000000000) (23974157842 / 1000000000000), orderedInterval (-20185014394 / 1000000000000) (-20185001689 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks5 :
    compactCertificate503.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2163117075188797 / 4000000000000)) (orderedInterval (32107712368 / 1000000000000) (32107712372 / 1000000000000), orderedInterval (12066638901 / 1000000000000) (12066638905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1911179536688737 / 4000000000000)) (orderedInterval (31806030493 / 1000000000000) (31806030494 / 1000000000000), orderedInterval (17877280574 / 1000000000000) (17877280575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (553934321532963 / 800000000000)) (orderedInterval (26868091844 / 1000000000000) (26868167442 / 1000000000000), orderedInterval (-14073582429 / 1000000000000) (-14073506831 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks6 :
    compactCertificate503.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1532211485326361 / 4000000000000)) (orderedInterval (21780518586 / 1000000000000) (21780518587 / 1000000000000), orderedInterval (34432748159 / 1000000000000) (34432748160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1298872644888721 / 4000000000000)) (orderedInterval (-41618632529 / 1000000000000) (-41618622978 / 1000000000000), orderedInterval (15177591712 / 1000000000000) (15177601263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (812774192580763 / 4000000000000)) (orderedInterval (12498540989 / 1000000000000) (12498541080 / 1000000000000), orderedInterval (-54591416871 / 1000000000000) (-54591416780 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks7 :
    compactCertificate503.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (437112663934821 / 4000000000000)) (orderedInterval (-8126802240 / 1000000000000) (-8126802239 / 1000000000000), orderedInterval (-75855477901 / 1000000000000) (-75855477899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1186845913107463 / 4000000000000)) (orderedInterval (37807857386 / 1000000000000) (37807954314 / 1000000000000), orderedInterval (-26824669610 / 1000000000000) (-26824572682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1620536627770151 / 4000000000000)) (orderedInterval (-24109529143 / 1000000000000) (-24109529142 / 1000000000000), orderedInterval (-31436275403 / 1000000000000) (-31436275402 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_stateChecks8 :
    compactCertificate503.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (685225807419237 / 4000000000000)) (orderedInterval (39107588814 / 1000000000000) (39107612822 / 1000000000000), orderedInterval (-46878041219 / 1000000000000) (-46878017211 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2785404864559877 / 4000000000000)) (orderedInterval (-8852565646 / 1000000000000) (-8852565639 / 1000000000000), orderedInterval (28917505140 / 1000000000000) (28917505146 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1860521362545643 / 4000000000000)) (orderedInterval (30301509977 / 1000000000000) (30301509978 / 1000000000000), orderedInterval (21192632545 / 1000000000000) (21192632546 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_states : ∀ j,
    BesselStateValid (compactCertificate503.point j) (compactCertificate503.state j) :=
  compactCertificate503.statesValid_of_checks3 compactCertificate503_stateChecks0
    compactCertificate503_stateChecks1 compactCertificate503_stateChecks2
    compactCertificate503_stateChecks3 compactCertificate503_stateChecks4
    compactCertificate503_stateChecks5 compactCertificate503_stateChecks6
    compactCertificate503_stateChecks7 compactCertificate503_stateChecks8

theorem compactCertificate503_chunkChecks0_0 :
    compactCertificate503.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (749 / 2) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40853488952 / 1000000000000) (-40853488918 / 1000000000000), orderedInterval (-5505156350 / 1000000000000) (-5505156316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1103420019977849 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8590888991 / 1000000000000) (8590888992 / 1000000000000), orderedInterval (47249700751 / 1000000000000) (47249700752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (356823363265817 / 800000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24573461339 / 1000000000000) (24573461340 / 1000000000000), orderedInterval (28668276305 / 1000000000000) (28668276306 / 1000000000000)))) (orderedInterval (-14670843732 / 1000000000000) (-14670843692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (321975209860843 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34939315981 / 1000000000000) (-34939314087 / 1000000000000), orderedInterval (81998919226 / 1000000000000) (81998921120 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (864870703245871 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12507931192 / 1000000000000) (-12507931191 / 1000000000000), orderedInterval (-52771693786 / 1000000000000) (-52771693785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2348292200624307 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12226984442 / 1000000000000) (-12226984441 / 1000000000000), orderedInterval (-30565677078 / 1000000000000) (-30565677077 / 1000000000000)))) (orderedInterval (791592291 / 1000000000000) (791592357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1729741406492491 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12045002248 / 1000000000000) (-12045002182 / 1000000000000), orderedInterval (36443200792 / 1000000000000) (36443200858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2963941382522743 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10180326116 / 1000000000000) (10180326117 / 1000000000000), orderedInterval (27479747198 / 1000000000000) (27479747199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2183225807419237 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1553420704 / 1000000000000) (-1553420703 / 1000000000000), orderedInterval (34118443943 / 1000000000000) (34118443944 / 1000000000000)))) (orderedInterval (-351545113 / 1000000000000) (-351545092 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks0_1 :
    compactCertificate503.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3349629830294251 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15852395204 / 1000000000000) (15852395428 / 1000000000000), orderedInterval (-22568911723 / 1000000000000) (-22568911498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1933909684205779 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16021464697 / 1000000000000) (16021464698 / 1000000000000), orderedInterval (32542069128 / 1000000000000) (32542069129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3431756671496111 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23890304591 / 1000000000000) (-23890304585 / 1000000000000), orderedInterval (-13073741951 / 1000000000000) (-13073741945 / 1000000000000)))) (orderedInterval (-5025868206 / 1000000000000) (-5025868017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3206392238278859 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26975241193 / 1000000000000) (-26975241113 / 1000000000000), orderedInterval (-8139429483 / 1000000000000) (-8139429403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2288232797013947 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29319126090 / 1000000000000) (29319126091 / 1000000000000), orderedInterval (15888110657 / 1000000000000) (15888110658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2594612109737613 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23974145137 / 1000000000000) (23974157842 / 1000000000000), orderedInterval (-20185014394 / 1000000000000) (-20185001689 / 1000000000000)))) (orderedInterval (3138163869 / 1000000000000) (3138163980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2163117075188797 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32107712368 / 1000000000000) (32107712372 / 1000000000000), orderedInterval (12066638901 / 1000000000000) (12066638905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1911179536688737 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31806030493 / 1000000000000) (31806030494 / 1000000000000), orderedInterval (17877280574 / 1000000000000) (17877280575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (553934321532963 / 800000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26868091844 / 1000000000000) (26868167442 / 1000000000000), orderedInterval (-14073582429 / 1000000000000) (-14073506831 / 1000000000000)))) (orderedInterval (-761454905 / 1000000000000) (-761452933 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks0_2 :
    compactCertificate503.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1532211485326361 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21780518586 / 1000000000000) (21780518587 / 1000000000000), orderedInterval (34432748159 / 1000000000000) (34432748160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1298872644888721 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41618632529 / 1000000000000) (-41618622978 / 1000000000000), orderedInterval (15177591712 / 1000000000000) (15177601263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (812774192580763 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12498540989 / 1000000000000) (12498541080 / 1000000000000), orderedInterval (-54591416871 / 1000000000000) (-54591416780 / 1000000000000)))) (orderedInterval (-720034734 / 1000000000000) (-720034096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (437112663934821 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8126802240 / 1000000000000) (-8126802239 / 1000000000000), orderedInterval (-75855477901 / 1000000000000) (-75855477899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1186845913107463 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37807857386 / 1000000000000) (37807954314 / 1000000000000), orderedInterval (-26824669610 / 1000000000000) (-26824572682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1620536627770151 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24109529143 / 1000000000000) (-24109529142 / 1000000000000), orderedInterval (-31436275403 / 1000000000000) (-31436275402 / 1000000000000)))) (orderedInterval (1140045559 / 1000000000000) (1140047803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (685225807419237 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39107588814 / 1000000000000) (39107612822 / 1000000000000), orderedInterval (-46878041219 / 1000000000000) (-46878017211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2785404864559877 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8852565646 / 1000000000000) (-8852565639 / 1000000000000), orderedInterval (28917505140 / 1000000000000) (28917505146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1860521362545643 / 4000000000000) 0 (IntervalRat.scale (749 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30301509977 / 1000000000000) (30301509978 / 1000000000000), orderedInterval (21192632545 / 1000000000000) (21192632546 / 1000000000000)))) (orderedInterval (-4728999185 / 1000000000000) (-4728998936 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks0 :
    compactCertificate503.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate503.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate503_chunkChecks0_0
    compactCertificate503_chunkChecks0_1 compactCertificate503_chunkChecks0_2

theorem compactCertificate503_chunkChecks1_0 :
    compactCertificate503.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (749 / 2) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40853488952 / 1000000000000) (-40853488918 / 1000000000000), orderedInterval (-5505156350 / 1000000000000) (-5505156316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1103420019977849 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8590888991 / 1000000000000) (8590888992 / 1000000000000), orderedInterval (47249700751 / 1000000000000) (47249700752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (356823363265817 / 800000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24573461339 / 1000000000000) (24573461340 / 1000000000000), orderedInterval (28668276305 / 1000000000000) (28668276306 / 1000000000000)))) (orderedInterval (145856351 / 1000000000000) (145856394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (321975209860843 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34939315981 / 1000000000000) (-34939314087 / 1000000000000), orderedInterval (81998919226 / 1000000000000) (81998921120 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (864870703245871 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12507931192 / 1000000000000) (-12507931191 / 1000000000000), orderedInterval (-52771693786 / 1000000000000) (-52771693785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2348292200624307 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12226984442 / 1000000000000) (-12226984441 / 1000000000000), orderedInterval (-30565677078 / 1000000000000) (-30565677077 / 1000000000000)))) (orderedInterval (2102637481 / 1000000000000) (2102637537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1729741406492491 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12045002248 / 1000000000000) (-12045002182 / 1000000000000), orderedInterval (36443200792 / 1000000000000) (36443200858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2963941382522743 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10180326116 / 1000000000000) (10180326117 / 1000000000000), orderedInterval (27479747198 / 1000000000000) (27479747199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2183225807419237 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1553420704 / 1000000000000) (-1553420703 / 1000000000000), orderedInterval (34118443943 / 1000000000000) (34118443944 / 1000000000000)))) (orderedInterval (-475272941 / 1000000000000) (-475272904 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks1_1 :
    compactCertificate503.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3349629830294251 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15852395204 / 1000000000000) (15852395428 / 1000000000000), orderedInterval (-22568911723 / 1000000000000) (-22568911498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1933909684205779 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16021464697 / 1000000000000) (16021464698 / 1000000000000), orderedInterval (32542069128 / 1000000000000) (32542069129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3431756671496111 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23890304591 / 1000000000000) (-23890304585 / 1000000000000), orderedInterval (-13073741951 / 1000000000000) (-13073741945 / 1000000000000)))) (orderedInterval (7822202369 / 1000000000000) (7822202768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3206392238278859 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26975241193 / 1000000000000) (-26975241113 / 1000000000000), orderedInterval (-8139429483 / 1000000000000) (-8139429403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2288232797013947 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29319126090 / 1000000000000) (29319126091 / 1000000000000), orderedInterval (15888110657 / 1000000000000) (15888110658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2594612109737613 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23974145137 / 1000000000000) (23974157842 / 1000000000000), orderedInterval (-20185014394 / 1000000000000) (-20185001689 / 1000000000000)))) (orderedInterval (2786438987 / 1000000000000) (2786439174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2163117075188797 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32107712368 / 1000000000000) (32107712372 / 1000000000000), orderedInterval (12066638901 / 1000000000000) (12066638905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1911179536688737 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31806030493 / 1000000000000) (31806030494 / 1000000000000), orderedInterval (17877280574 / 1000000000000) (17877280575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (553934321532963 / 800000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26868091844 / 1000000000000) (26868167442 / 1000000000000), orderedInterval (-14073582429 / 1000000000000) (-14073506831 / 1000000000000)))) (orderedInterval (-1770264183 / 1000000000000) (-1770260552 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks1_2 :
    compactCertificate503.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1532211485326361 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21780518586 / 1000000000000) (21780518587 / 1000000000000), orderedInterval (34432748159 / 1000000000000) (34432748160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1298872644888721 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41618632529 / 1000000000000) (-41618622978 / 1000000000000), orderedInterval (15177591712 / 1000000000000) (15177601263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (812774192580763 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12498540989 / 1000000000000) (12498541080 / 1000000000000), orderedInterval (-54591416871 / 1000000000000) (-54591416780 / 1000000000000)))) (orderedInterval (-7340412486 / 1000000000000) (-7340411928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (437112663934821 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8126802240 / 1000000000000) (-8126802239 / 1000000000000), orderedInterval (-75855477901 / 1000000000000) (-75855477899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1186845913107463 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37807857386 / 1000000000000) (37807954314 / 1000000000000), orderedInterval (-26824669610 / 1000000000000) (-26824572682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1620536627770151 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24109529143 / 1000000000000) (-24109529142 / 1000000000000), orderedInterval (-31436275403 / 1000000000000) (-31436275402 / 1000000000000)))) (orderedInterval (3497190296 / 1000000000000) (3497192080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (685225807419237 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39107588814 / 1000000000000) (39107612822 / 1000000000000), orderedInterval (-46878041219 / 1000000000000) (-46878017211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2785404864559877 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8852565646 / 1000000000000) (-8852565639 / 1000000000000), orderedInterval (28917505140 / 1000000000000) (28917505146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1860521362545643 / 4000000000000) 1 (IntervalRat.scale (749 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30301509977 / 1000000000000) (30301509978 / 1000000000000), orderedInterval (21192632545 / 1000000000000) (21192632546 / 1000000000000)))) (orderedInterval (-9444792479 / 1000000000000) (-9444792265 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks1 :
    compactCertificate503.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate503.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate503_chunkChecks1_0
    compactCertificate503_chunkChecks1_1 compactCertificate503_chunkChecks1_2

theorem compactCertificate503_chunkChecks2_0 :
    compactCertificate503.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (749 / 2) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40853488952 / 1000000000000) (-40853488918 / 1000000000000), orderedInterval (-5505156350 / 1000000000000) (-5505156316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1103420019977849 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8590888991 / 1000000000000) (8590888992 / 1000000000000), orderedInterval (47249700751 / 1000000000000) (47249700752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (356823363265817 / 800000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24573461339 / 1000000000000) (24573461340 / 1000000000000), orderedInterval (28668276305 / 1000000000000) (28668276306 / 1000000000000)))) (orderedInterval (14103625095 / 1000000000000) (14103625143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (321975209860843 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34939315981 / 1000000000000) (-34939314087 / 1000000000000), orderedInterval (81998919226 / 1000000000000) (81998921120 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (864870703245871 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12507931192 / 1000000000000) (-12507931191 / 1000000000000), orderedInterval (-52771693786 / 1000000000000) (-52771693785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2348292200624307 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12226984442 / 1000000000000) (-12226984441 / 1000000000000), orderedInterval (-30565677078 / 1000000000000) (-30565677077 / 1000000000000)))) (orderedInterval (-2006922773 / 1000000000000) (-2006922701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1729741406492491 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12045002248 / 1000000000000) (-12045002182 / 1000000000000), orderedInterval (36443200792 / 1000000000000) (36443200858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2963941382522743 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10180326116 / 1000000000000) (10180326117 / 1000000000000), orderedInterval (27479747198 / 1000000000000) (27479747199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2183225807419237 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1553420704 / 1000000000000) (-1553420703 / 1000000000000), orderedInterval (34118443943 / 1000000000000) (34118443944 / 1000000000000)))) (orderedInterval (1310286157 / 1000000000000) (1310286223 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks2_1 :
    compactCertificate503.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3349629830294251 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15852395204 / 1000000000000) (15852395428 / 1000000000000), orderedInterval (-22568911723 / 1000000000000) (-22568911498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1933909684205779 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16021464697 / 1000000000000) (16021464698 / 1000000000000), orderedInterval (32542069128 / 1000000000000) (32542069129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3431756671496111 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23890304591 / 1000000000000) (-23890304585 / 1000000000000), orderedInterval (-13073741951 / 1000000000000) (-13073741945 / 1000000000000)))) (orderedInterval (29908196918 / 1000000000000) (29908197781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3206392238278859 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26975241193 / 1000000000000) (-26975241113 / 1000000000000), orderedInterval (-8139429483 / 1000000000000) (-8139429403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2288232797013947 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29319126090 / 1000000000000) (29319126091 / 1000000000000), orderedInterval (15888110657 / 1000000000000) (15888110658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2594612109737613 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23974145137 / 1000000000000) (23974157842 / 1000000000000), orderedInterval (-20185014394 / 1000000000000) (-20185001689 / 1000000000000)))) (orderedInterval (-8343777710 / 1000000000000) (-8343777390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2163117075188797 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32107712368 / 1000000000000) (32107712372 / 1000000000000), orderedInterval (12066638901 / 1000000000000) (12066638905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1911179536688737 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31806030493 / 1000000000000) (31806030494 / 1000000000000), orderedInterval (17877280574 / 1000000000000) (17877280575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (553934321532963 / 800000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26868091844 / 1000000000000) (26868167442 / 1000000000000), orderedInterval (-14073582429 / 1000000000000) (-14073506831 / 1000000000000)))) (orderedInterval (-157361772 / 1000000000000) (-157355068 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks2_2 :
    compactCertificate503.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1532211485326361 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21780518586 / 1000000000000) (21780518587 / 1000000000000), orderedInterval (34432748159 / 1000000000000) (34432748160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1298872644888721 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41618632529 / 1000000000000) (-41618622978 / 1000000000000), orderedInterval (15177591712 / 1000000000000) (15177601263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (812774192580763 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12498540989 / 1000000000000) (12498541080 / 1000000000000), orderedInterval (-54591416871 / 1000000000000) (-54591416780 / 1000000000000)))) (orderedInterval (1772264049 / 1000000000000) (1772264541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (437112663934821 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8126802240 / 1000000000000) (-8126802239 / 1000000000000), orderedInterval (-75855477901 / 1000000000000) (-75855477899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1186845913107463 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37807857386 / 1000000000000) (37807954314 / 1000000000000), orderedInterval (-26824669610 / 1000000000000) (-26824572682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1620536627770151 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24109529143 / 1000000000000) (-24109529142 / 1000000000000), orderedInterval (-31436275403 / 1000000000000) (-31436275402 / 1000000000000)))) (orderedInterval (-1646074456 / 1000000000000) (-1646073030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (685225807419237 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39107588814 / 1000000000000) (39107612822 / 1000000000000), orderedInterval (-46878041219 / 1000000000000) (-46878017211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2785404864559877 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8852565646 / 1000000000000) (-8852565639 / 1000000000000), orderedInterval (28917505140 / 1000000000000) (28917505146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1860521362545643 / 4000000000000) 2 (IntervalRat.scale (749 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30301509977 / 1000000000000) (30301509978 / 1000000000000), orderedInterval (21192632545 / 1000000000000) (21192632546 / 1000000000000)))) (orderedInterval (6254511445 / 1000000000000) (6254511693 / 1000000000000))) = true
  rfl'

theorem compactCertificate503_chunkChecks2 :
    compactCertificate503.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate503.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate503_chunkChecks2_0
    compactCertificate503_chunkChecks2_1 compactCertificate503_chunkChecks2_2

theorem compactCertificate503_chunkChecks3_0 :
    compactCertificate503.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (749 / 2) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40853488952 / 1000000000000) (-40853488918 / 1000000000000), orderedInterval (-5505156350 / 1000000000000) (-5505156316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1103420019977849 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8590888991 / 1000000000000) (8590888992 / 1000000000000), orderedInterval (47249700751 / 1000000000000) (47249700752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (356823363265817 / 800000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24573461339 / 1000000000000) (24573461340 / 1000000000000), orderedInterval (28668276305 / 1000000000000) (28668276306 / 1000000000000)))) (orderedInterval (-873635222 / 1000000000000) (-873635168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (321975209860843 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34939315981 / 1000000000000) (-34939314087 / 1000000000000), orderedInterval (81998919226 / 1000000000000) (81998921120 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (864870703245871 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12507931192 / 1000000000000) (-12507931191 / 1000000000000), orderedInterval (-52771693786 / 1000000000000) (-52771693785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2348292200624307 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12226984442 / 1000000000000) (-12226984441 / 1000000000000), orderedInterval (-30565677078 / 1000000000000) (-30565677077 / 1000000000000)))) (orderedInterval (-7985673143 / 1000000000000) (-7985673036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1729741406492491 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12045002248 / 1000000000000) (-12045002182 / 1000000000000), orderedInterval (36443200792 / 1000000000000) (36443200858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2963941382522743 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10180326116 / 1000000000000) (10180326117 / 1000000000000), orderedInterval (27479747198 / 1000000000000) (27479747199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2183225807419237 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1553420704 / 1000000000000) (-1553420703 / 1000000000000), orderedInterval (34118443943 / 1000000000000) (34118443944 / 1000000000000)))) (orderedInterval (4009183844 / 1000000000000) (4009183963 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate503_chunkChecks3_1 :
    compactCertificate503.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3349629830294251 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15852395204 / 1000000000000) (15852395428 / 1000000000000), orderedInterval (-22568911723 / 1000000000000) (-22568911498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1933909684205779 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16021464697 / 1000000000000) (16021464698 / 1000000000000), orderedInterval (32542069128 / 1000000000000) (32542069129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3431756671496111 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23890304591 / 1000000000000) (-23890304585 / 1000000000000), orderedInterval (-13073741951 / 1000000000000) (-13073741945 / 1000000000000)))) (orderedInterval (-27758404846 / 1000000000000) (-27758402943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3206392238278859 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26975241193 / 1000000000000) (-26975241113 / 1000000000000), orderedInterval (-8139429483 / 1000000000000) (-8139429403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2288232797013947 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29319126090 / 1000000000000) (29319126091 / 1000000000000), orderedInterval (15888110657 / 1000000000000) (15888110658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2594612109737613 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23974145137 / 1000000000000) (23974157842 / 1000000000000), orderedInterval (-20185014394 / 1000000000000) (-20185001689 / 1000000000000)))) (orderedInterval (-7304445074 / 1000000000000) (-7304444521 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2163117075188797 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32107712368 / 1000000000000) (32107712372 / 1000000000000), orderedInterval (12066638901 / 1000000000000) (12066638905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1911179536688737 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31806030493 / 1000000000000) (31806030494 / 1000000000000), orderedInterval (17877280574 / 1000000000000) (17877280575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (553934321532963 / 800000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26868091844 / 1000000000000) (26868167442 / 1000000000000), orderedInterval (-14073582429 / 1000000000000) (-14073506831 / 1000000000000)))) (orderedInterval (3982917599 / 1000000000000) (3982929970 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate503_chunkChecks3_2 :
    compactCertificate503.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1532211485326361 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21780518586 / 1000000000000) (21780518587 / 1000000000000), orderedInterval (34432748159 / 1000000000000) (34432748160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1298872644888721 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41618632529 / 1000000000000) (-41618622978 / 1000000000000), orderedInterval (15177591712 / 1000000000000) (15177601263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (812774192580763 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12498540989 / 1000000000000) (12498541080 / 1000000000000), orderedInterval (-54591416871 / 1000000000000) (-54591416780 / 1000000000000)))) (orderedInterval (6730503961 / 1000000000000) (6730504396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (437112663934821 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8126802240 / 1000000000000) (-8126802239 / 1000000000000), orderedInterval (-75855477901 / 1000000000000) (-75855477899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1186845913107463 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37807857386 / 1000000000000) (37807954314 / 1000000000000), orderedInterval (-26824669610 / 1000000000000) (-26824572682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1620536627770151 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24109529143 / 1000000000000) (-24109529142 / 1000000000000), orderedInterval (-31436275403 / 1000000000000) (-31436275402 / 1000000000000)))) (orderedInterval (-3383191667 / 1000000000000) (-3383190528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (685225807419237 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39107588814 / 1000000000000) (39107612822 / 1000000000000), orderedInterval (-46878041219 / 1000000000000) (-46878017211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2785404864559877 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8852565646 / 1000000000000) (-8852565639 / 1000000000000), orderedInterval (28917505140 / 1000000000000) (28917505146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1860521362545643 / 4000000000000) 3 (IntervalRat.scale (749 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30301509977 / 1000000000000) (30301509978 / 1000000000000), orderedInterval (21192632545 / 1000000000000) (21192632546 / 1000000000000)))) (orderedInterval (22761370199 / 1000000000000) (22761370548 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate503_chunkChecks3 :
    compactCertificate503.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate503.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate503_chunkChecks3_0
    compactCertificate503_chunkChecks3_1 compactCertificate503_chunkChecks3_2

theorem compactCertificate503_chunkChecks4_0 :
    compactCertificate503.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (749 / 2) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40853488952 / 1000000000000) (-40853488918 / 1000000000000), orderedInterval (-5505156350 / 1000000000000) (-5505156316 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1103420019977849 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8590888991 / 1000000000000) (8590888992 / 1000000000000), orderedInterval (47249700751 / 1000000000000) (47249700752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (356823363265817 / 800000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24573461339 / 1000000000000) (24573461340 / 1000000000000), orderedInterval (28668276305 / 1000000000000) (28668276306 / 1000000000000)))) (orderedInterval (-13263139917 / 1000000000000) (-13263139858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (321975209860843 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-34939315981 / 1000000000000) (-34939314087 / 1000000000000), orderedInterval (81998919226 / 1000000000000) (81998921120 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (864870703245871 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12507931192 / 1000000000000) (-12507931191 / 1000000000000), orderedInterval (-52771693786 / 1000000000000) (-52771693785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2348292200624307 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-12226984442 / 1000000000000) (-12226984441 / 1000000000000), orderedInterval (-30565677078 / 1000000000000) (-30565677077 / 1000000000000)))) (orderedInterval (5241824436 / 1000000000000) (5241824600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1729741406492491 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-12045002248 / 1000000000000) (-12045002182 / 1000000000000), orderedInterval (36443200792 / 1000000000000) (36443200858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2963941382522743 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10180326116 / 1000000000000) (10180326117 / 1000000000000), orderedInterval (27479747198 / 1000000000000) (27479747199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2183225807419237 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1553420704 / 1000000000000) (-1553420703 / 1000000000000), orderedInterval (34118443943 / 1000000000000) (34118443944 / 1000000000000)))) (orderedInterval (-5003208388 / 1000000000000) (-5003208168 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate503_chunkChecks4_1 :
    compactCertificate503.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3349629830294251 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15852395204 / 1000000000000) (15852395428 / 1000000000000), orderedInterval (-22568911723 / 1000000000000) (-22568911498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1933909684205779 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (16021464697 / 1000000000000) (16021464698 / 1000000000000), orderedInterval (32542069128 / 1000000000000) (32542069129 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3431756671496111 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23890304591 / 1000000000000) (-23890304585 / 1000000000000), orderedInterval (-13073741951 / 1000000000000) (-13073741945 / 1000000000000)))) (orderedInterval (-160515339480 / 1000000000000) (-160515335250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3206392238278859 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26975241193 / 1000000000000) (-26975241113 / 1000000000000), orderedInterval (-8139429483 / 1000000000000) (-8139429403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2288232797013947 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29319126090 / 1000000000000) (29319126091 / 1000000000000), orderedInterval (15888110657 / 1000000000000) (15888110658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2594612109737613 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23974145137 / 1000000000000) (23974157842 / 1000000000000), orderedInterval (-20185014394 / 1000000000000) (-20185001689 / 1000000000000)))) (orderedInterval (24263773235 / 1000000000000) (24263774200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2163117075188797 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32107712368 / 1000000000000) (32107712372 / 1000000000000), orderedInterval (12066638901 / 1000000000000) (12066638905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1911179536688737 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31806030493 / 1000000000000) (31806030494 / 1000000000000), orderedInterval (17877280574 / 1000000000000) (17877280575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (553934321532963 / 800000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26868091844 / 1000000000000) (26868167442 / 1000000000000), orderedInterval (-14073582429 / 1000000000000) (-14073506831 / 1000000000000)))) (orderedInterval (4807473763 / 1000000000000) (4807496637 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate503_chunkChecks4_2 :
    compactCertificate503.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1532211485326361 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (21780518586 / 1000000000000) (21780518587 / 1000000000000), orderedInterval (34432748159 / 1000000000000) (34432748160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1298872644888721 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41618632529 / 1000000000000) (-41618622978 / 1000000000000), orderedInterval (15177591712 / 1000000000000) (15177601263 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (812774192580763 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12498540989 / 1000000000000) (12498541080 / 1000000000000), orderedInterval (-54591416871 / 1000000000000) (-54591416780 / 1000000000000)))) (orderedInterval (-2480969186 / 1000000000000) (-2480968799 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (437112663934821 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-8126802240 / 1000000000000) (-8126802239 / 1000000000000), orderedInterval (-75855477901 / 1000000000000) (-75855477899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1186845913107463 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37807857386 / 1000000000000) (37807954314 / 1000000000000), orderedInterval (-26824669610 / 1000000000000) (-26824572682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1620536627770151 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-24109529143 / 1000000000000) (-24109529142 / 1000000000000), orderedInterval (-31436275403 / 1000000000000) (-31436275402 / 1000000000000)))) (orderedInterval (2211780827 / 1000000000000) (2211781743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (685225807419237 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39107588814 / 1000000000000) (39107612822 / 1000000000000), orderedInterval (-46878041219 / 1000000000000) (-46878017211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2785404864559877 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8852565646 / 1000000000000) (-8852565639 / 1000000000000), orderedInterval (28917505140 / 1000000000000) (28917505146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1860521362545643 / 4000000000000) 4 (IntervalRat.scale (749 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30301509977 / 1000000000000) (30301509978 / 1000000000000), orderedInterval (21192632545 / 1000000000000) (21192632546 / 1000000000000)))) (orderedInterval (-5025613834 / 1000000000000) (-5025613287 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate503_chunkChecks4 :
    compactCertificate503.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate503.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate503_chunkChecks4_0
    compactCertificate503_chunkChecks4_1 compactCertificate503_chunkChecks4_2

theorem compactCertificate503_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate503.chunkCheck r b = true :=
  compactCertificate503.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate503_chunkChecks0
    · exact compactCertificate503_chunkChecks1
    · exact compactCertificate503_chunkChecks2
    · exact compactCertificate503_chunkChecks3
    · exact compactCertificate503_chunkChecks4)

theorem compactCertificate503_coefficient0 :
    compactCertificate503.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate503_coefficient1 :
    compactCertificate503.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate503_coefficient2 :
    compactCertificate503.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate503_coefficient3 :
    compactCertificate503.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate503_coefficient4 :
    compactCertificate503.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate503_coefficients : ∀ r : Fin 5,
    compactCertificate503.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate503_coefficient0
  · exact compactCertificate503_coefficient1
  · exact compactCertificate503_coefficient2
  · exact compactCertificate503_coefficient3
  · exact compactCertificate503_coefficient4

theorem compactCertificate503_lower : (1 : ℚ) ≤ compactCertificate503.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate503, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate503_proves {t : ℝ} (ht : t ∈ compactCertificate503.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate503.proves compactCertificate503_states compactCertificate503_chunks
    compactCertificate503_coefficients compactCertificate503_lower ht

end Erdos232
