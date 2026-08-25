/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate592 : CompactCertificate where
  left := 463
  right := 464
  center := 927 / 2
  grid := fun i =>
    match i.val with
    | 0 => 148
    | 1 => 109
    | 2 => 176
    | 3 => 32
    | 4 => 85
    | 5 => 231
    | 6 => 170
    | 7 => 292
    | 8 => 215
    | 9 => 330
    | 10 => 191
    | 11 => 338
    | 12 => 316
    | 13 => 225
    | 14 => 256
    | 15 => 213
    | 16 => 188
    | 17 => 273
    | 18 => 151
    | 19 => 128
    | 20 => 80
    | 21 => 43
    | 22 => 117
    | 23 => 160
    | 24 => 68
    | 25 => 274
    | _ => 183
  point := fun i =>
    match i.val with
    | 0 => 927 / 2
    | 1 => 1365648008704227 / 4000000000000
    | 2 => 441622507005891 / 800000000000
    | 3 => 398492682965289 / 4000000000000
    | 4 => 1070407399077333 / 4000000000000
    | 5 => 2906364312388161 / 4000000000000
    | 6 => 2140814798155593 / 4000000000000
    | 7 => 3668322645658989 / 4000000000000
    | 8 => 2702069857780551 / 4000000000000
    | 9 => 4145670030284073 / 4000000000000
    | 10 => 2393503707955617 / 4000000000000
    | 11 => 4247314331744853 / 4000000000000
    | 12 => 3968391995840457 / 4000000000000
    | 13 => 2832031779481881 / 4000000000000
    | 14 => 3211222197231999 / 4000000000000
    | 15 => 2677182281308431 / 4000000000000
    | 16 => 2365371736329051 / 4000000000000
    | 17 => 685576923980049 / 800000000000
    | 18 => 1896341851665603 / 4000000000000
    | 19 => 1607549989067883 / 4000000000000
    | 20 => 1005930142219449 / 4000000000000
    | 21 => 540992576058183 / 4000000000000
    | 22 => 1468900082043549 / 4000000000000
    | 23 => 2005657481899773 / 4000000000000
    | 24 => 848069857780551 / 4000000000000
    | 25 => 3447356888447271 / 4000000000000
    | _ => 2302674636955689 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-23031222280 / 1000000000000) (-23031218019 / 1000000000000), orderedInterval (29060484922 / 1000000000000) (29060489183 / 1000000000000))
    | 1 => (orderedInterval (10120282932 / 1000000000000) (10120282971 / 1000000000000), orderedInterval (-41993969396 / 1000000000000) (-41993969357 / 1000000000000))
    | 2 => (orderedInterval (-3626773069 / 1000000000000) (-3626773067 / 1000000000000), orderedInterval (33768428092 / 1000000000000) (33768428093 / 1000000000000))
    | 3 => (orderedInterval (-9859306683 / 1000000000000) (-9859306639 / 1000000000000), orderedInterval (79378860000 / 1000000000000) (79378860044 / 1000000000000))
    | 4 => (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))
    | 5 => (orderedInterval (-29459341039 / 1000000000000) (-29459335130 / 1000000000000), orderedInterval (2904812165 / 1000000000000) (2904818074 / 1000000000000))
    | 6 => (orderedInterval (32429614287 / 1000000000000) (32429640670 / 1000000000000), orderedInterval (-11769536147 / 1000000000000) (-11769509763 / 1000000000000))
    | 7 => (orderedInterval (13111305829 / 1000000000000) (13111305830 / 1000000000000), orderedInterval (22846177304 / 1000000000000) (22846177305 / 1000000000000))
    | 8 => (orderedInterval (-23270021546 / 1000000000000) (-23270021545 / 1000000000000), orderedInterval (-20005862624 / 1000000000000) (-20005862623 / 1000000000000))
    | 9 => (orderedInterval (11383378152 / 1000000000000) (11383378153 / 1000000000000), orderedInterval (22009708743 / 1000000000000) (22009708744 / 1000000000000))
    | 10 => (orderedInterval (25203599174 / 1000000000000) (25203617357 / 1000000000000), orderedInterval (-20725918289 / 1000000000000) (-20725900106 / 1000000000000))
    | 11 => (orderedInterval (16789526821 / 1000000000000) (16789526822 / 1000000000000), orderedInterval (17815174947 / 1000000000000) (17815174948 / 1000000000000))
    | 12 => (orderedInterval (3534665602 / 1000000000000) (3534665603 / 1000000000000), orderedInterval (25082010729 / 1000000000000) (25082010730 / 1000000000000))
    | 13 => (orderedInterval (-28021265790 / 1000000000000) (-28021198838 / 1000000000000), orderedInterval (10695929359 / 1000000000000) (10695996312 / 1000000000000))
    | 14 => (orderedInterval (-17197025722 / 1000000000000) (-17197025222 / 1000000000000), orderedInterval (22309950007 / 1000000000000) (22309950506 / 1000000000000))
    | 15 => (orderedInterval (-24566161017 / 1000000000000) (-24566161016 / 1000000000000), orderedInterval (-18627893598 / 1000000000000) (-18627893597 / 1000000000000))
    | 16 => (orderedInterval (32747826462 / 1000000000000) (32747826894 / 1000000000000), orderedInterval (2008383321 / 1000000000000) (2008383753 / 1000000000000))
    | 17 => (orderedInterval (-2764763070 / 1000000000000) (-2764763069 / 1000000000000), orderedInterval (-27113476578 / 1000000000000) (-27113476577 / 1000000000000))
    | 18 => (orderedInterval (-17249412943 / 1000000000000) (-17249412942 / 1000000000000), orderedInterval (-32312841445 / 1000000000000) (-32312841444 / 1000000000000))
    | 19 => (orderedInterval (20759883237 / 1000000000000) (20759883238 / 1000000000000), orderedInterval (33931533510 / 1000000000000) (33931533511 / 1000000000000))
    | 20 => (orderedInterval (40631909116 / 1000000000000) (40631909117 / 1000000000000), orderedInterval (29592664442 / 1000000000000) (29592664443 / 1000000000000))
    | 21 => (orderedInterval (-55571510761 / 1000000000000) (-55571510760 / 1000000000000), orderedInterval (-40029459336 / 1000000000000) (-40029459335 / 1000000000000))
    | 22 => (orderedInterval (-17875290357 / 1000000000000) (-17875290356 / 1000000000000), orderedInterval (-37579795279 / 1000000000000) (-37579795278 / 1000000000000))
    | 23 => (orderedInterval (-15668739288 / 1000000000000) (-15668739021 / 1000000000000), orderedInterval (32017796810 / 1000000000000) (32017797078 / 1000000000000))
    | 24 => (orderedInterval (-40288934308 / 1000000000000) (-40288870411 / 1000000000000), orderedInterval (37236326610 / 1000000000000) (37236390507 / 1000000000000))
    | 25 => (orderedInterval (26283914705 / 1000000000000) (26283966848 / 1000000000000), orderedInterval (-6931206154 / 1000000000000) (-6931154011 / 1000000000000))
    | _ => (orderedInterval (-33241329137 / 1000000000000) (-33241328540 / 1000000000000), orderedInterval (-915824621 / 1000000000000) (-915824025 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-9247292049 / 1000000000000) (-9247290327 / 1000000000000)
      | 1 => orderedInterval (463055159 / 1000000000000) (463055636 / 1000000000000)
      | 2 => orderedInterval (-966795652 / 1000000000000) (-966795626 / 1000000000000)
      | 3 => orderedInterval (2231420513 / 1000000000000) (2231422044 / 1000000000000)
      | 4 => orderedInterval (-2626555999 / 1000000000000) (-2626549610 / 1000000000000)
      | 5 => orderedInterval (-2228520110 / 1000000000000) (-2228520041 / 1000000000000)
      | 6 => orderedInterval (2905825035 / 1000000000000) (2905825152 / 1000000000000)
      | 7 => orderedInterval (2632503119 / 1000000000000) (2632503195 / 1000000000000)
      | _ => orderedInterval (3854518444 / 1000000000000) (3854523314 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13590375495 / 1000000000000) (13590377221 / 1000000000000)
      | 1 => orderedInterval (-730714106 / 1000000000000) (-730713384 / 1000000000000)
      | 2 => orderedInterval (-2098923756 / 1000000000000) (-2098923711 / 1000000000000)
      | 3 => orderedInterval (-4925666499 / 1000000000000) (-4925664379 / 1000000000000)
      | 4 => orderedInterval (380234328 / 1000000000000) (380244094 / 1000000000000)
      | 5 => orderedInterval (-1740789639 / 1000000000000) (-1740789543 / 1000000000000)
      | 6 => orderedInterval (4142056745 / 1000000000000) (4142056853 / 1000000000000)
      | 7 => orderedInterval (-1763369689 / 1000000000000) (-1763369616 / 1000000000000)
      | _ => orderedInterval (1365194642 / 1000000000000) (1365203029 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9350167194 / 1000000000000) (9350168929 / 1000000000000)
      | 1 => orderedInterval (-4570453359 / 1000000000000) (-4570452237 / 1000000000000)
      | 2 => orderedInterval (2782285689 / 1000000000000) (2782285770 / 1000000000000)
      | 3 => orderedInterval (-5514237619 / 1000000000000) (-5514234553 / 1000000000000)
      | 4 => orderedInterval (6213237961 / 1000000000000) (6213252911 / 1000000000000)
      | 5 => orderedInterval (3887689112 / 1000000000000) (3887689248 / 1000000000000)
      | 6 => orderedInterval (-2400425017 / 1000000000000) (-2400424914 / 1000000000000)
      | 7 => orderedInterval (-1743454462 / 1000000000000) (-1743454388 / 1000000000000)
      | _ => orderedInterval (-2175720896 / 1000000000000) (-2175705684 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-14729962703 / 1000000000000) (-14729960962 / 1000000000000)
      | 1 => orderedInterval (887882330 / 1000000000000) (887884082 / 1000000000000)
      | 2 => orderedInterval (6949073985 / 1000000000000) (6949074131 / 1000000000000)
      | 3 => orderedInterval (16592021322 / 1000000000000) (16592026018 / 1000000000000)
      | 4 => orderedInterval (1408697140 / 1000000000000) (1408720002 / 1000000000000)
      | 5 => orderedInterval (5265713461 / 1000000000000) (5265713660 / 1000000000000)
      | 6 => orderedInterval (-4425449678 / 1000000000000) (-4425449578 / 1000000000000)
      | 7 => orderedInterval (2667952195 / 1000000000000) (2667952272 / 1000000000000)
      | _ => orderedInterval (-3973202337 / 1000000000000) (-3973174357 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9465624147 / 1000000000000) (-9465622393 / 1000000000000)
      | 1 => orderedInterval (12450334598 / 1000000000000) (12450337343 / 1000000000000)
      | 2 => orderedInterval (-8765298265 / 1000000000000) (-8765297993 / 1000000000000)
      | 3 => orderedInterval (20287157926 / 1000000000000) (20287165659 / 1000000000000)
      | 4 => orderedInterval (-14988767576 / 1000000000000) (-14988732550 / 1000000000000)
      | 5 => orderedInterval (-7048577508 / 1000000000000) (-7048577209 / 1000000000000)
      | 6 => orderedInterval (2488348715 / 1000000000000) (2488348814 / 1000000000000)
      | 7 => orderedInterval (1800353587 / 1000000000000) (1800353669 / 1000000000000)
      | _ => orderedInterval (-10728367236 / 1000000000000) (-10728315437 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2981841540 / 1000000000000) (-2981826263 / 1000000000000)
    | 1 => orderedInterval (8218397521 / 1000000000000) (8218420564 / 1000000000000)
    | 2 => orderedInterval (5829088603 / 1000000000000) (5829125082 / 1000000000000)
    | 3 => orderedInterval (10642725715 / 1000000000000) (10642785268 / 1000000000000)
    | _ => orderedInterval (-13970439906 / 1000000000000) (-13970340097 / 1000000000000)

theorem compactCertificate592_stateChecks0 :
    compactCertificate592.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (927 / 2)) (orderedInterval (-23031222280 / 1000000000000) (-23031218019 / 1000000000000), orderedInterval (29060484922 / 1000000000000) (29060489183 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1365648008704227 / 4000000000000)) (orderedInterval (10120282932 / 1000000000000) (10120282971 / 1000000000000), orderedInterval (-41993969396 / 1000000000000) (-41993969357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (441622507005891 / 800000000000)) (orderedInterval (-3626773069 / 1000000000000) (-3626773067 / 1000000000000), orderedInterval (33768428092 / 1000000000000) (33768428093 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks1 :
    compactCertificate592.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (398492682965289 / 4000000000000)) (orderedInterval (-9859306683 / 1000000000000) (-9859306639 / 1000000000000), orderedInterval (79378860000 / 1000000000000) (79378860044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1070407399077333 / 4000000000000)) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2906364312388161 / 4000000000000)) (orderedInterval (-29459341039 / 1000000000000) (-29459335130 / 1000000000000), orderedInterval (2904812165 / 1000000000000) (2904818074 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks2 :
    compactCertificate592.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2140814798155593 / 4000000000000)) (orderedInterval (32429614287 / 1000000000000) (32429640670 / 1000000000000), orderedInterval (-11769536147 / 1000000000000) (-11769509763 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (3668322645658989 / 4000000000000)) (orderedInterval (13111305829 / 1000000000000) (13111305830 / 1000000000000), orderedInterval (22846177304 / 1000000000000) (22846177305 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2702069857780551 / 4000000000000)) (orderedInterval (-23270021546 / 1000000000000) (-23270021545 / 1000000000000), orderedInterval (-20005862624 / 1000000000000) (-20005862623 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks3 :
    compactCertificate592.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 330 12 (4145670030284073 / 4000000000000)) (orderedInterval (11383378152 / 1000000000000) (11383378153 / 1000000000000), orderedInterval (22009708743 / 1000000000000) (22009708744 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2393503707955617 / 4000000000000)) (orderedInterval (25203599174 / 1000000000000) (25203617357 / 1000000000000), orderedInterval (-20725918289 / 1000000000000) (-20725900106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 338 12 (4247314331744853 / 4000000000000)) (orderedInterval (16789526821 / 1000000000000) (16789526822 / 1000000000000), orderedInterval (17815174947 / 1000000000000) (17815174948 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks4 :
    compactCertificate592.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 316 12 (3968391995840457 / 4000000000000)) (orderedInterval (3534665602 / 1000000000000) (3534665603 / 1000000000000), orderedInterval (25082010729 / 1000000000000) (25082010730 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2832031779481881 / 4000000000000)) (orderedInterval (-28021265790 / 1000000000000) (-28021198838 / 1000000000000), orderedInterval (10695929359 / 1000000000000) (10695996312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3211222197231999 / 4000000000000)) (orderedInterval (-17197025722 / 1000000000000) (-17197025222 / 1000000000000), orderedInterval (22309950007 / 1000000000000) (22309950506 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks5 :
    compactCertificate592.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2677182281308431 / 4000000000000)) (orderedInterval (-24566161017 / 1000000000000) (-24566161016 / 1000000000000), orderedInterval (-18627893598 / 1000000000000) (-18627893597 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2365371736329051 / 4000000000000)) (orderedInterval (32747826462 / 1000000000000) (32747826894 / 1000000000000), orderedInterval (2008383321 / 1000000000000) (2008383753 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (685576923980049 / 800000000000)) (orderedInterval (-2764763070 / 1000000000000) (-2764763069 / 1000000000000), orderedInterval (-27113476578 / 1000000000000) (-27113476577 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks6 :
    compactCertificate592.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1896341851665603 / 4000000000000)) (orderedInterval (-17249412943 / 1000000000000) (-17249412942 / 1000000000000), orderedInterval (-32312841445 / 1000000000000) (-32312841444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1607549989067883 / 4000000000000)) (orderedInterval (20759883237 / 1000000000000) (20759883238 / 1000000000000), orderedInterval (33931533510 / 1000000000000) (33931533511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1005930142219449 / 4000000000000)) (orderedInterval (40631909116 / 1000000000000) (40631909117 / 1000000000000), orderedInterval (29592664442 / 1000000000000) (29592664443 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks7 :
    compactCertificate592.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (540992576058183 / 4000000000000)) (orderedInterval (-55571510761 / 1000000000000) (-55571510760 / 1000000000000), orderedInterval (-40029459336 / 1000000000000) (-40029459335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1468900082043549 / 4000000000000)) (orderedInterval (-17875290357 / 1000000000000) (-17875290356 / 1000000000000), orderedInterval (-37579795279 / 1000000000000) (-37579795278 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2005657481899773 / 4000000000000)) (orderedInterval (-15668739288 / 1000000000000) (-15668739021 / 1000000000000), orderedInterval (32017796810 / 1000000000000) (32017797078 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_stateChecks8 :
    compactCertificate592.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (848069857780551 / 4000000000000)) (orderedInterval (-40288934308 / 1000000000000) (-40288870411 / 1000000000000), orderedInterval (37236326610 / 1000000000000) (37236390507 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (3447356888447271 / 4000000000000)) (orderedInterval (26283914705 / 1000000000000) (26283966848 / 1000000000000), orderedInterval (-6931206154 / 1000000000000) (-6931154011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2302674636955689 / 4000000000000)) (orderedInterval (-33241329137 / 1000000000000) (-33241328540 / 1000000000000), orderedInterval (-915824621 / 1000000000000) (-915824025 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_states : ∀ j,
    BesselStateValid (compactCertificate592.point j) (compactCertificate592.state j) :=
  compactCertificate592.statesValid_of_checks3 compactCertificate592_stateChecks0
    compactCertificate592_stateChecks1 compactCertificate592_stateChecks2
    compactCertificate592_stateChecks3 compactCertificate592_stateChecks4
    compactCertificate592_stateChecks5 compactCertificate592_stateChecks6
    compactCertificate592_stateChecks7 compactCertificate592_stateChecks8

theorem compactCertificate592_chunkChecks0_0 :
    compactCertificate592.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (927 / 2) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23031222280 / 1000000000000) (-23031218019 / 1000000000000), orderedInterval (29060484922 / 1000000000000) (29060489183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1365648008704227 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10120282932 / 1000000000000) (10120282971 / 1000000000000), orderedInterval (-41993969396 / 1000000000000) (-41993969357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (441622507005891 / 800000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3626773069 / 1000000000000) (-3626773067 / 1000000000000), orderedInterval (33768428092 / 1000000000000) (33768428093 / 1000000000000)))) (orderedInterval (-9247292049 / 1000000000000) (-9247290327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (398492682965289 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9859306683 / 1000000000000) (-9859306639 / 1000000000000), orderedInterval (79378860000 / 1000000000000) (79378860044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2906364312388161 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29459341039 / 1000000000000) (-29459335130 / 1000000000000), orderedInterval (2904812165 / 1000000000000) (2904818074 / 1000000000000)))) (orderedInterval (463055159 / 1000000000000) (463055636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2140814798155593 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32429614287 / 1000000000000) (32429640670 / 1000000000000), orderedInterval (-11769536147 / 1000000000000) (-11769509763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3668322645658989 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13111305829 / 1000000000000) (13111305830 / 1000000000000), orderedInterval (22846177304 / 1000000000000) (22846177305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2702069857780551 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23270021546 / 1000000000000) (-23270021545 / 1000000000000), orderedInterval (-20005862624 / 1000000000000) (-20005862623 / 1000000000000)))) (orderedInterval (-966795652 / 1000000000000) (-966795626 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks0_1 :
    compactCertificate592.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4145670030284073 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11383378152 / 1000000000000) (11383378153 / 1000000000000), orderedInterval (22009708743 / 1000000000000) (22009708744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2393503707955617 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25203599174 / 1000000000000) (25203617357 / 1000000000000), orderedInterval (-20725918289 / 1000000000000) (-20725900106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4247314331744853 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16789526821 / 1000000000000) (16789526822 / 1000000000000), orderedInterval (17815174947 / 1000000000000) (17815174948 / 1000000000000)))) (orderedInterval (2231420513 / 1000000000000) (2231422044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3968391995840457 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3534665602 / 1000000000000) (3534665603 / 1000000000000), orderedInterval (25082010729 / 1000000000000) (25082010730 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2832031779481881 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28021265790 / 1000000000000) (-28021198838 / 1000000000000), orderedInterval (10695929359 / 1000000000000) (10695996312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3211222197231999 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17197025722 / 1000000000000) (-17197025222 / 1000000000000), orderedInterval (22309950007 / 1000000000000) (22309950506 / 1000000000000)))) (orderedInterval (-2626555999 / 1000000000000) (-2626549610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2677182281308431 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24566161017 / 1000000000000) (-24566161016 / 1000000000000), orderedInterval (-18627893598 / 1000000000000) (-18627893597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2365371736329051 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32747826462 / 1000000000000) (32747826894 / 1000000000000), orderedInterval (2008383321 / 1000000000000) (2008383753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (685576923980049 / 800000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2764763070 / 1000000000000) (-2764763069 / 1000000000000), orderedInterval (-27113476578 / 1000000000000) (-27113476577 / 1000000000000)))) (orderedInterval (-2228520110 / 1000000000000) (-2228520041 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks0_2 :
    compactCertificate592.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1896341851665603 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17249412943 / 1000000000000) (-17249412942 / 1000000000000), orderedInterval (-32312841445 / 1000000000000) (-32312841444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1607549989067883 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20759883237 / 1000000000000) (20759883238 / 1000000000000), orderedInterval (33931533510 / 1000000000000) (33931533511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1005930142219449 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40631909116 / 1000000000000) (40631909117 / 1000000000000), orderedInterval (29592664442 / 1000000000000) (29592664443 / 1000000000000)))) (orderedInterval (2905825035 / 1000000000000) (2905825152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (540992576058183 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55571510761 / 1000000000000) (-55571510760 / 1000000000000), orderedInterval (-40029459336 / 1000000000000) (-40029459335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1468900082043549 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17875290357 / 1000000000000) (-17875290356 / 1000000000000), orderedInterval (-37579795279 / 1000000000000) (-37579795278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2005657481899773 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15668739288 / 1000000000000) (-15668739021 / 1000000000000), orderedInterval (32017796810 / 1000000000000) (32017797078 / 1000000000000)))) (orderedInterval (2632503119 / 1000000000000) (2632503195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (848069857780551 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40288934308 / 1000000000000) (-40288870411 / 1000000000000), orderedInterval (37236326610 / 1000000000000) (37236390507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3447356888447271 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26283914705 / 1000000000000) (26283966848 / 1000000000000), orderedInterval (-6931206154 / 1000000000000) (-6931154011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2302674636955689 / 4000000000000) 0 (IntervalRat.scale (927 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33241329137 / 1000000000000) (-33241328540 / 1000000000000), orderedInterval (-915824621 / 1000000000000) (-915824025 / 1000000000000)))) (orderedInterval (3854518444 / 1000000000000) (3854523314 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks0 :
    compactCertificate592.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate592.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate592_chunkChecks0_0
    compactCertificate592_chunkChecks0_1 compactCertificate592_chunkChecks0_2

theorem compactCertificate592_chunkChecks1_0 :
    compactCertificate592.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (927 / 2) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23031222280 / 1000000000000) (-23031218019 / 1000000000000), orderedInterval (29060484922 / 1000000000000) (29060489183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1365648008704227 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10120282932 / 1000000000000) (10120282971 / 1000000000000), orderedInterval (-41993969396 / 1000000000000) (-41993969357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (441622507005891 / 800000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3626773069 / 1000000000000) (-3626773067 / 1000000000000), orderedInterval (33768428092 / 1000000000000) (33768428093 / 1000000000000)))) (orderedInterval (13590375495 / 1000000000000) (13590377221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (398492682965289 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9859306683 / 1000000000000) (-9859306639 / 1000000000000), orderedInterval (79378860000 / 1000000000000) (79378860044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2906364312388161 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29459341039 / 1000000000000) (-29459335130 / 1000000000000), orderedInterval (2904812165 / 1000000000000) (2904818074 / 1000000000000)))) (orderedInterval (-730714106 / 1000000000000) (-730713384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2140814798155593 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32429614287 / 1000000000000) (32429640670 / 1000000000000), orderedInterval (-11769536147 / 1000000000000) (-11769509763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3668322645658989 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13111305829 / 1000000000000) (13111305830 / 1000000000000), orderedInterval (22846177304 / 1000000000000) (22846177305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2702069857780551 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23270021546 / 1000000000000) (-23270021545 / 1000000000000), orderedInterval (-20005862624 / 1000000000000) (-20005862623 / 1000000000000)))) (orderedInterval (-2098923756 / 1000000000000) (-2098923711 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks1_1 :
    compactCertificate592.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4145670030284073 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11383378152 / 1000000000000) (11383378153 / 1000000000000), orderedInterval (22009708743 / 1000000000000) (22009708744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2393503707955617 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25203599174 / 1000000000000) (25203617357 / 1000000000000), orderedInterval (-20725918289 / 1000000000000) (-20725900106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4247314331744853 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16789526821 / 1000000000000) (16789526822 / 1000000000000), orderedInterval (17815174947 / 1000000000000) (17815174948 / 1000000000000)))) (orderedInterval (-4925666499 / 1000000000000) (-4925664379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3968391995840457 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3534665602 / 1000000000000) (3534665603 / 1000000000000), orderedInterval (25082010729 / 1000000000000) (25082010730 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2832031779481881 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28021265790 / 1000000000000) (-28021198838 / 1000000000000), orderedInterval (10695929359 / 1000000000000) (10695996312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3211222197231999 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17197025722 / 1000000000000) (-17197025222 / 1000000000000), orderedInterval (22309950007 / 1000000000000) (22309950506 / 1000000000000)))) (orderedInterval (380234328 / 1000000000000) (380244094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2677182281308431 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24566161017 / 1000000000000) (-24566161016 / 1000000000000), orderedInterval (-18627893598 / 1000000000000) (-18627893597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2365371736329051 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32747826462 / 1000000000000) (32747826894 / 1000000000000), orderedInterval (2008383321 / 1000000000000) (2008383753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (685576923980049 / 800000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2764763070 / 1000000000000) (-2764763069 / 1000000000000), orderedInterval (-27113476578 / 1000000000000) (-27113476577 / 1000000000000)))) (orderedInterval (-1740789639 / 1000000000000) (-1740789543 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks1_2 :
    compactCertificate592.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1896341851665603 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17249412943 / 1000000000000) (-17249412942 / 1000000000000), orderedInterval (-32312841445 / 1000000000000) (-32312841444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1607549989067883 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20759883237 / 1000000000000) (20759883238 / 1000000000000), orderedInterval (33931533510 / 1000000000000) (33931533511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1005930142219449 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40631909116 / 1000000000000) (40631909117 / 1000000000000), orderedInterval (29592664442 / 1000000000000) (29592664443 / 1000000000000)))) (orderedInterval (4142056745 / 1000000000000) (4142056853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (540992576058183 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55571510761 / 1000000000000) (-55571510760 / 1000000000000), orderedInterval (-40029459336 / 1000000000000) (-40029459335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1468900082043549 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17875290357 / 1000000000000) (-17875290356 / 1000000000000), orderedInterval (-37579795279 / 1000000000000) (-37579795278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2005657481899773 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15668739288 / 1000000000000) (-15668739021 / 1000000000000), orderedInterval (32017796810 / 1000000000000) (32017797078 / 1000000000000)))) (orderedInterval (-1763369689 / 1000000000000) (-1763369616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (848069857780551 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40288934308 / 1000000000000) (-40288870411 / 1000000000000), orderedInterval (37236326610 / 1000000000000) (37236390507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3447356888447271 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26283914705 / 1000000000000) (26283966848 / 1000000000000), orderedInterval (-6931206154 / 1000000000000) (-6931154011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2302674636955689 / 4000000000000) 1 (IntervalRat.scale (927 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33241329137 / 1000000000000) (-33241328540 / 1000000000000), orderedInterval (-915824621 / 1000000000000) (-915824025 / 1000000000000)))) (orderedInterval (1365194642 / 1000000000000) (1365203029 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks1 :
    compactCertificate592.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate592.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate592_chunkChecks1_0
    compactCertificate592_chunkChecks1_1 compactCertificate592_chunkChecks1_2

theorem compactCertificate592_chunkChecks2_0 :
    compactCertificate592.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (927 / 2) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23031222280 / 1000000000000) (-23031218019 / 1000000000000), orderedInterval (29060484922 / 1000000000000) (29060489183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1365648008704227 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10120282932 / 1000000000000) (10120282971 / 1000000000000), orderedInterval (-41993969396 / 1000000000000) (-41993969357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (441622507005891 / 800000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3626773069 / 1000000000000) (-3626773067 / 1000000000000), orderedInterval (33768428092 / 1000000000000) (33768428093 / 1000000000000)))) (orderedInterval (9350167194 / 1000000000000) (9350168929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (398492682965289 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9859306683 / 1000000000000) (-9859306639 / 1000000000000), orderedInterval (79378860000 / 1000000000000) (79378860044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2906364312388161 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29459341039 / 1000000000000) (-29459335130 / 1000000000000), orderedInterval (2904812165 / 1000000000000) (2904818074 / 1000000000000)))) (orderedInterval (-4570453359 / 1000000000000) (-4570452237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2140814798155593 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32429614287 / 1000000000000) (32429640670 / 1000000000000), orderedInterval (-11769536147 / 1000000000000) (-11769509763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3668322645658989 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13111305829 / 1000000000000) (13111305830 / 1000000000000), orderedInterval (22846177304 / 1000000000000) (22846177305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2702069857780551 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23270021546 / 1000000000000) (-23270021545 / 1000000000000), orderedInterval (-20005862624 / 1000000000000) (-20005862623 / 1000000000000)))) (orderedInterval (2782285689 / 1000000000000) (2782285770 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks2_1 :
    compactCertificate592.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4145670030284073 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11383378152 / 1000000000000) (11383378153 / 1000000000000), orderedInterval (22009708743 / 1000000000000) (22009708744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2393503707955617 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25203599174 / 1000000000000) (25203617357 / 1000000000000), orderedInterval (-20725918289 / 1000000000000) (-20725900106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4247314331744853 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16789526821 / 1000000000000) (16789526822 / 1000000000000), orderedInterval (17815174947 / 1000000000000) (17815174948 / 1000000000000)))) (orderedInterval (-5514237619 / 1000000000000) (-5514234553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3968391995840457 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3534665602 / 1000000000000) (3534665603 / 1000000000000), orderedInterval (25082010729 / 1000000000000) (25082010730 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2832031779481881 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28021265790 / 1000000000000) (-28021198838 / 1000000000000), orderedInterval (10695929359 / 1000000000000) (10695996312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3211222197231999 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17197025722 / 1000000000000) (-17197025222 / 1000000000000), orderedInterval (22309950007 / 1000000000000) (22309950506 / 1000000000000)))) (orderedInterval (6213237961 / 1000000000000) (6213252911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2677182281308431 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24566161017 / 1000000000000) (-24566161016 / 1000000000000), orderedInterval (-18627893598 / 1000000000000) (-18627893597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2365371736329051 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32747826462 / 1000000000000) (32747826894 / 1000000000000), orderedInterval (2008383321 / 1000000000000) (2008383753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (685576923980049 / 800000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2764763070 / 1000000000000) (-2764763069 / 1000000000000), orderedInterval (-27113476578 / 1000000000000) (-27113476577 / 1000000000000)))) (orderedInterval (3887689112 / 1000000000000) (3887689248 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks2_2 :
    compactCertificate592.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1896341851665603 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17249412943 / 1000000000000) (-17249412942 / 1000000000000), orderedInterval (-32312841445 / 1000000000000) (-32312841444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1607549989067883 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20759883237 / 1000000000000) (20759883238 / 1000000000000), orderedInterval (33931533510 / 1000000000000) (33931533511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1005930142219449 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40631909116 / 1000000000000) (40631909117 / 1000000000000), orderedInterval (29592664442 / 1000000000000) (29592664443 / 1000000000000)))) (orderedInterval (-2400425017 / 1000000000000) (-2400424914 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (540992576058183 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55571510761 / 1000000000000) (-55571510760 / 1000000000000), orderedInterval (-40029459336 / 1000000000000) (-40029459335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1468900082043549 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17875290357 / 1000000000000) (-17875290356 / 1000000000000), orderedInterval (-37579795279 / 1000000000000) (-37579795278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2005657481899773 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15668739288 / 1000000000000) (-15668739021 / 1000000000000), orderedInterval (32017796810 / 1000000000000) (32017797078 / 1000000000000)))) (orderedInterval (-1743454462 / 1000000000000) (-1743454388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (848069857780551 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40288934308 / 1000000000000) (-40288870411 / 1000000000000), orderedInterval (37236326610 / 1000000000000) (37236390507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3447356888447271 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26283914705 / 1000000000000) (26283966848 / 1000000000000), orderedInterval (-6931206154 / 1000000000000) (-6931154011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2302674636955689 / 4000000000000) 2 (IntervalRat.scale (927 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33241329137 / 1000000000000) (-33241328540 / 1000000000000), orderedInterval (-915824621 / 1000000000000) (-915824025 / 1000000000000)))) (orderedInterval (-2175720896 / 1000000000000) (-2175705684 / 1000000000000))) = true
  rfl'

theorem compactCertificate592_chunkChecks2 :
    compactCertificate592.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate592.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate592_chunkChecks2_0
    compactCertificate592_chunkChecks2_1 compactCertificate592_chunkChecks2_2

theorem compactCertificate592_chunkChecks3_0 :
    compactCertificate592.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (927 / 2) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23031222280 / 1000000000000) (-23031218019 / 1000000000000), orderedInterval (29060484922 / 1000000000000) (29060489183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1365648008704227 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10120282932 / 1000000000000) (10120282971 / 1000000000000), orderedInterval (-41993969396 / 1000000000000) (-41993969357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (441622507005891 / 800000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3626773069 / 1000000000000) (-3626773067 / 1000000000000), orderedInterval (33768428092 / 1000000000000) (33768428093 / 1000000000000)))) (orderedInterval (-14729962703 / 1000000000000) (-14729960962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (398492682965289 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9859306683 / 1000000000000) (-9859306639 / 1000000000000), orderedInterval (79378860000 / 1000000000000) (79378860044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2906364312388161 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29459341039 / 1000000000000) (-29459335130 / 1000000000000), orderedInterval (2904812165 / 1000000000000) (2904818074 / 1000000000000)))) (orderedInterval (887882330 / 1000000000000) (887884082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2140814798155593 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32429614287 / 1000000000000) (32429640670 / 1000000000000), orderedInterval (-11769536147 / 1000000000000) (-11769509763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3668322645658989 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13111305829 / 1000000000000) (13111305830 / 1000000000000), orderedInterval (22846177304 / 1000000000000) (22846177305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2702069857780551 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23270021546 / 1000000000000) (-23270021545 / 1000000000000), orderedInterval (-20005862624 / 1000000000000) (-20005862623 / 1000000000000)))) (orderedInterval (6949073985 / 1000000000000) (6949074131 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate592_chunkChecks3_1 :
    compactCertificate592.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4145670030284073 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11383378152 / 1000000000000) (11383378153 / 1000000000000), orderedInterval (22009708743 / 1000000000000) (22009708744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2393503707955617 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25203599174 / 1000000000000) (25203617357 / 1000000000000), orderedInterval (-20725918289 / 1000000000000) (-20725900106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4247314331744853 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16789526821 / 1000000000000) (16789526822 / 1000000000000), orderedInterval (17815174947 / 1000000000000) (17815174948 / 1000000000000)))) (orderedInterval (16592021322 / 1000000000000) (16592026018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3968391995840457 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3534665602 / 1000000000000) (3534665603 / 1000000000000), orderedInterval (25082010729 / 1000000000000) (25082010730 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2832031779481881 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28021265790 / 1000000000000) (-28021198838 / 1000000000000), orderedInterval (10695929359 / 1000000000000) (10695996312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3211222197231999 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17197025722 / 1000000000000) (-17197025222 / 1000000000000), orderedInterval (22309950007 / 1000000000000) (22309950506 / 1000000000000)))) (orderedInterval (1408697140 / 1000000000000) (1408720002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2677182281308431 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24566161017 / 1000000000000) (-24566161016 / 1000000000000), orderedInterval (-18627893598 / 1000000000000) (-18627893597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2365371736329051 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32747826462 / 1000000000000) (32747826894 / 1000000000000), orderedInterval (2008383321 / 1000000000000) (2008383753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (685576923980049 / 800000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2764763070 / 1000000000000) (-2764763069 / 1000000000000), orderedInterval (-27113476578 / 1000000000000) (-27113476577 / 1000000000000)))) (orderedInterval (5265713461 / 1000000000000) (5265713660 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate592_chunkChecks3_2 :
    compactCertificate592.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1896341851665603 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17249412943 / 1000000000000) (-17249412942 / 1000000000000), orderedInterval (-32312841445 / 1000000000000) (-32312841444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1607549989067883 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20759883237 / 1000000000000) (20759883238 / 1000000000000), orderedInterval (33931533510 / 1000000000000) (33931533511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1005930142219449 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40631909116 / 1000000000000) (40631909117 / 1000000000000), orderedInterval (29592664442 / 1000000000000) (29592664443 / 1000000000000)))) (orderedInterval (-4425449678 / 1000000000000) (-4425449578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (540992576058183 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55571510761 / 1000000000000) (-55571510760 / 1000000000000), orderedInterval (-40029459336 / 1000000000000) (-40029459335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1468900082043549 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17875290357 / 1000000000000) (-17875290356 / 1000000000000), orderedInterval (-37579795279 / 1000000000000) (-37579795278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2005657481899773 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15668739288 / 1000000000000) (-15668739021 / 1000000000000), orderedInterval (32017796810 / 1000000000000) (32017797078 / 1000000000000)))) (orderedInterval (2667952195 / 1000000000000) (2667952272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (848069857780551 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40288934308 / 1000000000000) (-40288870411 / 1000000000000), orderedInterval (37236326610 / 1000000000000) (37236390507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3447356888447271 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26283914705 / 1000000000000) (26283966848 / 1000000000000), orderedInterval (-6931206154 / 1000000000000) (-6931154011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2302674636955689 / 4000000000000) 3 (IntervalRat.scale (927 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33241329137 / 1000000000000) (-33241328540 / 1000000000000), orderedInterval (-915824621 / 1000000000000) (-915824025 / 1000000000000)))) (orderedInterval (-3973202337 / 1000000000000) (-3973174357 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate592_chunkChecks3 :
    compactCertificate592.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate592.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate592_chunkChecks3_0
    compactCertificate592_chunkChecks3_1 compactCertificate592_chunkChecks3_2

theorem compactCertificate592_chunkChecks4_0 :
    compactCertificate592.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (927 / 2) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23031222280 / 1000000000000) (-23031218019 / 1000000000000), orderedInterval (29060484922 / 1000000000000) (29060489183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1365648008704227 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10120282932 / 1000000000000) (10120282971 / 1000000000000), orderedInterval (-41993969396 / 1000000000000) (-41993969357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (441622507005891 / 800000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-3626773069 / 1000000000000) (-3626773067 / 1000000000000), orderedInterval (33768428092 / 1000000000000) (33768428093 / 1000000000000)))) (orderedInterval (-9465624147 / 1000000000000) (-9465622393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (398492682965289 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9859306683 / 1000000000000) (-9859306639 / 1000000000000), orderedInterval (79378860000 / 1000000000000) (79378860044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1070407399077333 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47605635137 / 1000000000000) (-47605635133 / 1000000000000), orderedInterval (-10526180239 / 1000000000000) (-10526180235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2906364312388161 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29459341039 / 1000000000000) (-29459335130 / 1000000000000), orderedInterval (2904812165 / 1000000000000) (2904818074 / 1000000000000)))) (orderedInterval (12450334598 / 1000000000000) (12450337343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2140814798155593 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32429614287 / 1000000000000) (32429640670 / 1000000000000), orderedInterval (-11769536147 / 1000000000000) (-11769509763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3668322645658989 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13111305829 / 1000000000000) (13111305830 / 1000000000000), orderedInterval (22846177304 / 1000000000000) (22846177305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2702069857780551 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23270021546 / 1000000000000) (-23270021545 / 1000000000000), orderedInterval (-20005862624 / 1000000000000) (-20005862623 / 1000000000000)))) (orderedInterval (-8765298265 / 1000000000000) (-8765297993 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate592_chunkChecks4_1 :
    compactCertificate592.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4145670030284073 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11383378152 / 1000000000000) (11383378153 / 1000000000000), orderedInterval (22009708743 / 1000000000000) (22009708744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2393503707955617 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25203599174 / 1000000000000) (25203617357 / 1000000000000), orderedInterval (-20725918289 / 1000000000000) (-20725900106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4247314331744853 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16789526821 / 1000000000000) (16789526822 / 1000000000000), orderedInterval (17815174947 / 1000000000000) (17815174948 / 1000000000000)))) (orderedInterval (20287157926 / 1000000000000) (20287165659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3968391995840457 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3534665602 / 1000000000000) (3534665603 / 1000000000000), orderedInterval (25082010729 / 1000000000000) (25082010730 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2832031779481881 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28021265790 / 1000000000000) (-28021198838 / 1000000000000), orderedInterval (10695929359 / 1000000000000) (10695996312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3211222197231999 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17197025722 / 1000000000000) (-17197025222 / 1000000000000), orderedInterval (22309950007 / 1000000000000) (22309950506 / 1000000000000)))) (orderedInterval (-14988767576 / 1000000000000) (-14988732550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2677182281308431 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24566161017 / 1000000000000) (-24566161016 / 1000000000000), orderedInterval (-18627893598 / 1000000000000) (-18627893597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2365371736329051 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32747826462 / 1000000000000) (32747826894 / 1000000000000), orderedInterval (2008383321 / 1000000000000) (2008383753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (685576923980049 / 800000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2764763070 / 1000000000000) (-2764763069 / 1000000000000), orderedInterval (-27113476578 / 1000000000000) (-27113476577 / 1000000000000)))) (orderedInterval (-7048577508 / 1000000000000) (-7048577209 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate592_chunkChecks4_2 :
    compactCertificate592.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1896341851665603 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17249412943 / 1000000000000) (-17249412942 / 1000000000000), orderedInterval (-32312841445 / 1000000000000) (-32312841444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1607549989067883 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20759883237 / 1000000000000) (20759883238 / 1000000000000), orderedInterval (33931533510 / 1000000000000) (33931533511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1005930142219449 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40631909116 / 1000000000000) (40631909117 / 1000000000000), orderedInterval (29592664442 / 1000000000000) (29592664443 / 1000000000000)))) (orderedInterval (2488348715 / 1000000000000) (2488348814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (540992576058183 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55571510761 / 1000000000000) (-55571510760 / 1000000000000), orderedInterval (-40029459336 / 1000000000000) (-40029459335 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1468900082043549 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17875290357 / 1000000000000) (-17875290356 / 1000000000000), orderedInterval (-37579795279 / 1000000000000) (-37579795278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2005657481899773 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15668739288 / 1000000000000) (-15668739021 / 1000000000000), orderedInterval (32017796810 / 1000000000000) (32017797078 / 1000000000000)))) (orderedInterval (1800353587 / 1000000000000) (1800353669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (848069857780551 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40288934308 / 1000000000000) (-40288870411 / 1000000000000), orderedInterval (37236326610 / 1000000000000) (37236390507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3447356888447271 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26283914705 / 1000000000000) (26283966848 / 1000000000000), orderedInterval (-6931206154 / 1000000000000) (-6931154011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2302674636955689 / 4000000000000) 4 (IntervalRat.scale (927 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33241329137 / 1000000000000) (-33241328540 / 1000000000000), orderedInterval (-915824621 / 1000000000000) (-915824025 / 1000000000000)))) (orderedInterval (-10728367236 / 1000000000000) (-10728315437 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate592_chunkChecks4 :
    compactCertificate592.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate592.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate592_chunkChecks4_0
    compactCertificate592_chunkChecks4_1 compactCertificate592_chunkChecks4_2

theorem compactCertificate592_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate592.chunkCheck r b = true :=
  compactCertificate592.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate592_chunkChecks0
    · exact compactCertificate592_chunkChecks1
    · exact compactCertificate592_chunkChecks2
    · exact compactCertificate592_chunkChecks3
    · exact compactCertificate592_chunkChecks4)

theorem compactCertificate592_coefficient0 :
    compactCertificate592.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate592_coefficient1 :
    compactCertificate592.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate592_coefficient2 :
    compactCertificate592.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate592_coefficient3 :
    compactCertificate592.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate592_coefficient4 :
    compactCertificate592.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate592_coefficients : ∀ r : Fin 5,
    compactCertificate592.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate592_coefficient0
  · exact compactCertificate592_coefficient1
  · exact compactCertificate592_coefficient2
  · exact compactCertificate592_coefficient3
  · exact compactCertificate592_coefficient4

theorem compactCertificate592_lower : (1 : ℚ) ≤ compactCertificate592.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate592, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate592_proves {t : ℝ} (ht : t ∈ compactCertificate592.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate592.proves compactCertificate592_states compactCertificate592_chunks
    compactCertificate592_coefficients compactCertificate592_lower ht

end Erdos232
