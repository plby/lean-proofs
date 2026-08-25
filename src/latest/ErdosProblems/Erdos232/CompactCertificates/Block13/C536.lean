/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate536 : CompactCertificate where
  left := 407
  right := 408
  center := 815 / 2
  grid := fun i =>
    match i.val with
    | 0 => 130
    | 1 => 96
    | 2 => 155
    | 3 => 28
    | 4 => 75
    | 5 => 203
    | 6 => 150
    | 7 => 257
    | 8 => 189
    | 9 => 290
    | 10 => 168
    | 11 => 297
    | 12 => 278
    | 13 => 198
    | 14 => 225
    | 15 => 187
    | 16 => 166
    | 17 => 240
    | 18 => 133
    | 19 => 113
    | 20 => 70
    | 21 => 38
    | 22 => 103
    | 23 => 140
    | 24 => 59
    | 25 => 241
    | _ => 161
  point := fun i =>
    match i.val with
    | 0 => 815 / 2
    | 1 => 240130124507863 / 800000000000
    | 2 => 77653148481079 / 160000000000
    | 3 => 70069371438341 / 800000000000
    | 4 => 188216187755777 / 800000000000
    | 5 => 511043563019709 / 800000000000
    | 6 => 376432375511717 / 800000000000
    | 7 => 645023291523641 / 800000000000
    | 8 => 475121237128619 / 800000000000
    | 9 => 728958160664837 / 800000000000
    | 10 => 420864190287773 / 800000000000
    | 11 => 746830891126657 / 800000000000
    | 12 => 697786294845733 / 800000000000
    | 13 => 497973225518389 / 800000000000
    | 14 => 564648563267331 / 800000000000
    | 15 => 470745104480339 / 800000000000
    | 16 => 415917576075119 / 800000000000
    | 17 => 120549124712781 / 160000000000
    | 18 => 333445223108407 / 800000000000
    | 19 => 282665208433727 / 800000000000
    | 20 => 176878762871381 / 800000000000
    | 21 => 95125986944427 / 800000000000
    | 22 => 258285559194281 / 800000000000
    | 23 => 352666849568137 / 800000000000
    | 24 => 149121237128619 / 800000000000
    | 25 => 606169549964299 / 800000000000
    | _ => 404893167015941 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-4808321380 / 1000000000000) (-4808321376 / 1000000000000), orderedInterval (39237752859 / 1000000000000) (39237752863 / 1000000000000))
    | 1 => (orderedInterval (-27696689979 / 1000000000000) (-27696682238 / 1000000000000), orderedInterval (36840294105 / 1000000000000) (36840301847 / 1000000000000))
    | 2 => (orderedInterval (26714958211 / 1000000000000) (26714977054 / 1000000000000), orderedInterval (-24482185820 / 1000000000000) (-24482166977 / 1000000000000))
    | 3 => (orderedInterval (33677355796 / 1000000000000) (33677355797 / 1000000000000), orderedInterval (78129964372 / 1000000000000) (78129964373 / 1000000000000))
    | 4 => (orderedInterval (-21951826948 / 1000000000000) (-21951826947 / 1000000000000), orderedInterval (-47112969523 / 1000000000000) (-47112969522 / 1000000000000))
    | 5 => (orderedInterval (-30377745970 / 1000000000000) (-30377723921 / 1000000000000), orderedInterval (8612886150 / 1000000000000) (8612908199 / 1000000000000))
    | 6 => (orderedInterval (3185192036 / 1000000000000) (3185192037 / 1000000000000), orderedInterval (36640982609 / 1000000000000) (36640982610 / 1000000000000))
    | 7 => (orderedInterval (8971177570 / 1000000000000) (8971177574 / 1000000000000), orderedInterval (-26634410473 / 1000000000000) (-26634410469 / 1000000000000))
    | 8 => (orderedInterval (-26161320451 / 1000000000000) (-26161320450 / 1000000000000), orderedInterval (-19663333424 / 1000000000000) (-19663333423 / 1000000000000))
    | 9 => (orderedInterval (21046999150 / 1000000000000) (21046999151 / 1000000000000), orderedInterval (15978648473 / 1000000000000) (15978648475 / 1000000000000))
    | 10 => (orderedInterval (-27722031224 / 1000000000000) (-27721994534 / 1000000000000), orderedInterval (21040823505 / 1000000000000) (21040860195 / 1000000000000))
    | 11 => (orderedInterval (-24948176931 / 1000000000000) (-24948176745 / 1000000000000), orderedInterval (-7702272462 / 1000000000000) (-7702272275 / 1000000000000))
    | 12 => (orderedInterval (-9127480799 / 1000000000000) (-9127480796 / 1000000000000), orderedInterval (25432831810 / 1000000000000) (25432831814 / 1000000000000))
    | 13 => (orderedInterval (29992703985 / 1000000000000) (29992703993 / 1000000000000), orderedInterval (11074322883 / 1000000000000) (11074322891 / 1000000000000))
    | 14 => (orderedInterval (7791119303 / 1000000000000) (7791119307 / 1000000000000), orderedInterval (-29010143364 / 1000000000000) (-29010143360 / 1000000000000))
    | 15 => (orderedInterval (-32429364377 / 1000000000000) (-32429358449 / 1000000000000), orderedInterval (5525653457 / 1000000000000) (5525659384 / 1000000000000))
    | 16 => (orderedInterval (-25638714507 / 1000000000000) (-25638699651 / 1000000000000), orderedInterval (23839940321 / 1000000000000) (23839955177 / 1000000000000))
    | 17 => (orderedInterval (6769026366 / 1000000000000) (6769026367 / 1000000000000), orderedInterval (28264576515 / 1000000000000) (28264576516 / 1000000000000))
    | 18 => (orderedInterval (9297237457 / 1000000000000) (9297237480 / 1000000000000), orderedInterval (-37970830370 / 1000000000000) (-37970830347 / 1000000000000))
    | 19 => (orderedInterval (32807815319 / 1000000000000) (32807871871 / 1000000000000), orderedInterval (-26979859810 / 1000000000000) (-26979803257 / 1000000000000))
    | 20 => (orderedInterval (49402659875 / 1000000000000) (49402669454 / 1000000000000), orderedInterval (-21057400359 / 1000000000000) (-21057390779 / 1000000000000))
    | 21 => (orderedInterval (22412417095 / 1000000000000) (22412417096 / 1000000000000), orderedInterval (69559404416 / 1000000000000) (69559404417 / 1000000000000))
    | 22 => (orderedInterval (-2570369111 / 1000000000000) (-2570369110 / 1000000000000), orderedInterval (-44326910256 / 1000000000000) (-44326910255 / 1000000000000))
    | 23 => (orderedInterval (37044567673 / 1000000000000) (37044572593 / 1000000000000), orderedInterval (-8517056365 / 1000000000000) (-8517051445 / 1000000000000))
    | 24 => (orderedInterval (-56453625497 / 1000000000000) (-56453623700 / 1000000000000), orderedInterval (15260743591 / 1000000000000) (15260745387 / 1000000000000))
    | 25 => (orderedInterval (-28422750384 / 1000000000000) (-28422750161 / 1000000000000), orderedInterval (-5667558538 / 1000000000000) (-5667558315 / 1000000000000))
    | _ => (orderedInterval (-31690853920 / 1000000000000) (-31690853919 / 1000000000000), orderedInterval (-15891686613 / 1000000000000) (-15891686612 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-596265501 / 1000000000000) (-596264292 / 1000000000000)
      | 1 => orderedInterval (992666500 / 1000000000000) (992668117 / 1000000000000)
      | 2 => orderedInterval (-908974521 / 1000000000000) (-908974497 / 1000000000000)
      | 3 => orderedInterval (-9340302443 / 1000000000000) (-9340299536 / 1000000000000)
      | 4 => orderedInterval (2961547668 / 1000000000000) (2961547718 / 1000000000000)
      | 5 => orderedInterval (1266047778 / 1000000000000) (1266048736 / 1000000000000)
      | 6 => orderedInterval (-1735165180 / 1000000000000) (-1735161561 / 1000000000000)
      | 7 => orderedInterval (-3194588502 / 1000000000000) (-3194588076 / 1000000000000)
      | _ => orderedInterval (7919386201 / 1000000000000) (7919386343 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14094289998 / 1000000000000) (14094291402 / 1000000000000)
      | 1 => orderedInterval (-2135171413 / 1000000000000) (-2135168900 / 1000000000000)
      | 2 => orderedInterval (932838116 / 1000000000000) (932838157 / 1000000000000)
      | 3 => orderedInterval (-6844426632 / 1000000000000) (-6844422726 / 1000000000000)
      | 4 => orderedInterval (871165471 / 1000000000000) (871165552 / 1000000000000)
      | 5 => orderedInterval (-310408826 / 1000000000000) (-310407586 / 1000000000000)
      | 6 => orderedInterval (7162020905 / 1000000000000) (7162023948 / 1000000000000)
      | 7 => orderedInterval (1128094183 / 1000000000000) (1128094635 / 1000000000000)
      | _ => orderedInterval (4603206463 / 1000000000000) (4603206661 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-212410614 / 1000000000000) (-212408965 / 1000000000000)
      | 1 => orderedInterval (-5017633956 / 1000000000000) (-5017630021 / 1000000000000)
      | 2 => orderedInterval (2423973854 / 1000000000000) (2423973925 / 1000000000000)
      | 3 => orderedInterval (40751926288 / 1000000000000) (40751931684 / 1000000000000)
      | 4 => orderedInterval (-7256585348 / 1000000000000) (-7256585215 / 1000000000000)
      | 5 => orderedInterval (-2199074049 / 1000000000000) (-2199072435 / 1000000000000)
      | 6 => orderedInterval (2460249356 / 1000000000000) (2460251955 / 1000000000000)
      | 7 => orderedInterval (3318385244 / 1000000000000) (3318385730 / 1000000000000)
      | _ => orderedInterval (-17111614397 / 1000000000000) (-17111614098 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13261986874 / 1000000000000) (-13261984928 / 1000000000000)
      | 1 => orderedInterval (2710483191 / 1000000000000) (2710489354 / 1000000000000)
      | 2 => orderedInterval (-4898156543 / 1000000000000) (-4898156413 / 1000000000000)
      | 3 => orderedInterval (41453281775 / 1000000000000) (41453289532 / 1000000000000)
      | 4 => orderedInterval (25020635 / 1000000000000) (25020860 / 1000000000000)
      | 5 => orderedInterval (-1927587921 / 1000000000000) (-1927585816 / 1000000000000)
      | 6 => orderedInterval (-7388737770 / 1000000000000) (-7388735535 / 1000000000000)
      | 7 => orderedInterval (-1302742030 / 1000000000000) (-1302741506 / 1000000000000)
      | _ => orderedInterval (-8645292372 / 1000000000000) (-8645291893 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (1237533420 / 1000000000000) (1237535727 / 1000000000000)
      | 1 => orderedInterval (12938190138 / 1000000000000) (12938199811 / 1000000000000)
      | 2 => orderedInterval (-7069428545 / 1000000000000) (-7069428305 / 1000000000000)
      | 3 => orderedInterval (-197087394272 / 1000000000000) (-197087382467 / 1000000000000)
      | 4 => orderedInterval (18545267437 / 1000000000000) (18545267826 / 1000000000000)
      | 5 => orderedInterval (4293946373 / 1000000000000) (4293949138 / 1000000000000)
      | 6 => orderedInterval (-2500996818 / 1000000000000) (-2500994880 / 1000000000000)
      | 7 => orderedInterval (-3861927714 / 1000000000000) (-3861927147 / 1000000000000)
      | _ => orderedInterval (41833288992 / 1000000000000) (41833289790 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2635648000 / 1000000000000) (-2635637048 / 1000000000000)
    | 1 => orderedInterval (19501608265 / 1000000000000) (19501621143 / 1000000000000)
    | 2 => orderedInterval (17157216378 / 1000000000000) (17157232560 / 1000000000000)
    | 3 => orderedInterval (6764282091 / 1000000000000) (6764303655 / 1000000000000)
    | _ => orderedInterval (-131671520989 / 1000000000000) (-131671490507 / 1000000000000)

theorem compactCertificate536_stateChecks0 :
    compactCertificate536.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (815 / 2)) (orderedInterval (-4808321380 / 1000000000000) (-4808321376 / 1000000000000), orderedInterval (39237752859 / 1000000000000) (39237752863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (240130124507863 / 800000000000)) (orderedInterval (-27696689979 / 1000000000000) (-27696682238 / 1000000000000), orderedInterval (36840294105 / 1000000000000) (36840301847 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (77653148481079 / 160000000000)) (orderedInterval (26714958211 / 1000000000000) (26714977054 / 1000000000000), orderedInterval (-24482185820 / 1000000000000) (-24482166977 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks1 :
    compactCertificate536.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (70069371438341 / 800000000000)) (orderedInterval (33677355796 / 1000000000000) (33677355797 / 1000000000000), orderedInterval (78129964372 / 1000000000000) (78129964373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (188216187755777 / 800000000000)) (orderedInterval (-21951826948 / 1000000000000) (-21951826947 / 1000000000000), orderedInterval (-47112969523 / 1000000000000) (-47112969522 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (511043563019709 / 800000000000)) (orderedInterval (-30377745970 / 1000000000000) (-30377723921 / 1000000000000), orderedInterval (8612886150 / 1000000000000) (8612908199 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks2 :
    compactCertificate536.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (376432375511717 / 800000000000)) (orderedInterval (3185192036 / 1000000000000) (3185192037 / 1000000000000), orderedInterval (36640982609 / 1000000000000) (36640982610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (645023291523641 / 800000000000)) (orderedInterval (8971177570 / 1000000000000) (8971177574 / 1000000000000), orderedInterval (-26634410473 / 1000000000000) (-26634410469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (475121237128619 / 800000000000)) (orderedInterval (-26161320451 / 1000000000000) (-26161320450 / 1000000000000), orderedInterval (-19663333424 / 1000000000000) (-19663333423 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks3 :
    compactCertificate536.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (728958160664837 / 800000000000)) (orderedInterval (21046999150 / 1000000000000) (21046999151 / 1000000000000), orderedInterval (15978648473 / 1000000000000) (15978648475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (420864190287773 / 800000000000)) (orderedInterval (-27722031224 / 1000000000000) (-27721994534 / 1000000000000), orderedInterval (21040823505 / 1000000000000) (21040860195 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 297 12 (746830891126657 / 800000000000)) (orderedInterval (-24948176931 / 1000000000000) (-24948176745 / 1000000000000), orderedInterval (-7702272462 / 1000000000000) (-7702272275 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks4 :
    compactCertificate536.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (697786294845733 / 800000000000)) (orderedInterval (-9127480799 / 1000000000000) (-9127480796 / 1000000000000), orderedInterval (25432831810 / 1000000000000) (25432831814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (497973225518389 / 800000000000)) (orderedInterval (29992703985 / 1000000000000) (29992703993 / 1000000000000), orderedInterval (11074322883 / 1000000000000) (11074322891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (564648563267331 / 800000000000)) (orderedInterval (7791119303 / 1000000000000) (7791119307 / 1000000000000), orderedInterval (-29010143364 / 1000000000000) (-29010143360 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks5 :
    compactCertificate536.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (470745104480339 / 800000000000)) (orderedInterval (-32429364377 / 1000000000000) (-32429358449 / 1000000000000), orderedInterval (5525653457 / 1000000000000) (5525659384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (415917576075119 / 800000000000)) (orderedInterval (-25638714507 / 1000000000000) (-25638699651 / 1000000000000), orderedInterval (23839940321 / 1000000000000) (23839955177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (120549124712781 / 160000000000)) (orderedInterval (6769026366 / 1000000000000) (6769026367 / 1000000000000), orderedInterval (28264576515 / 1000000000000) (28264576516 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks6 :
    compactCertificate536.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (333445223108407 / 800000000000)) (orderedInterval (9297237457 / 1000000000000) (9297237480 / 1000000000000), orderedInterval (-37970830370 / 1000000000000) (-37970830347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (282665208433727 / 800000000000)) (orderedInterval (32807815319 / 1000000000000) (32807871871 / 1000000000000), orderedInterval (-26979859810 / 1000000000000) (-26979803257 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176878762871381 / 800000000000)) (orderedInterval (49402659875 / 1000000000000) (49402669454 / 1000000000000), orderedInterval (-21057400359 / 1000000000000) (-21057390779 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks7 :
    compactCertificate536.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (95125986944427 / 800000000000)) (orderedInterval (22412417095 / 1000000000000) (22412417096 / 1000000000000), orderedInterval (69559404416 / 1000000000000) (69559404417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (258285559194281 / 800000000000)) (orderedInterval (-2570369111 / 1000000000000) (-2570369110 / 1000000000000), orderedInterval (-44326910256 / 1000000000000) (-44326910255 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (352666849568137 / 800000000000)) (orderedInterval (37044567673 / 1000000000000) (37044572593 / 1000000000000), orderedInterval (-8517056365 / 1000000000000) (-8517051445 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_stateChecks8 :
    compactCertificate536.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (149121237128619 / 800000000000)) (orderedInterval (-56453625497 / 1000000000000) (-56453623700 / 1000000000000), orderedInterval (15260743591 / 1000000000000) (15260745387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (606169549964299 / 800000000000)) (orderedInterval (-28422750384 / 1000000000000) (-28422750161 / 1000000000000), orderedInterval (-5667558538 / 1000000000000) (-5667558315 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (404893167015941 / 800000000000)) (orderedInterval (-31690853920 / 1000000000000) (-31690853919 / 1000000000000), orderedInterval (-15891686613 / 1000000000000) (-15891686612 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_states : ∀ j,
    BesselStateValid (compactCertificate536.point j) (compactCertificate536.state j) :=
  compactCertificate536.statesValid_of_checks3 compactCertificate536_stateChecks0
    compactCertificate536_stateChecks1 compactCertificate536_stateChecks2
    compactCertificate536_stateChecks3 compactCertificate536_stateChecks4
    compactCertificate536_stateChecks5 compactCertificate536_stateChecks6
    compactCertificate536_stateChecks7 compactCertificate536_stateChecks8

theorem compactCertificate536_chunkChecks0_0 :
    compactCertificate536.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (815 / 2) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4808321380 / 1000000000000) (-4808321376 / 1000000000000), orderedInterval (39237752859 / 1000000000000) (39237752863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (240130124507863 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27696689979 / 1000000000000) (-27696682238 / 1000000000000), orderedInterval (36840294105 / 1000000000000) (36840301847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (77653148481079 / 160000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26714958211 / 1000000000000) (26714977054 / 1000000000000), orderedInterval (-24482185820 / 1000000000000) (-24482166977 / 1000000000000)))) (orderedInterval (-596265501 / 1000000000000) (-596264292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (70069371438341 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33677355796 / 1000000000000) (33677355797 / 1000000000000), orderedInterval (78129964372 / 1000000000000) (78129964373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (188216187755777 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21951826948 / 1000000000000) (-21951826947 / 1000000000000), orderedInterval (-47112969523 / 1000000000000) (-47112969522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (511043563019709 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30377745970 / 1000000000000) (-30377723921 / 1000000000000), orderedInterval (8612886150 / 1000000000000) (8612908199 / 1000000000000)))) (orderedInterval (992666500 / 1000000000000) (992668117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (376432375511717 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3185192036 / 1000000000000) (3185192037 / 1000000000000), orderedInterval (36640982609 / 1000000000000) (36640982610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (645023291523641 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (8971177570 / 1000000000000) (8971177574 / 1000000000000), orderedInterval (-26634410473 / 1000000000000) (-26634410469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (475121237128619 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26161320451 / 1000000000000) (-26161320450 / 1000000000000), orderedInterval (-19663333424 / 1000000000000) (-19663333423 / 1000000000000)))) (orderedInterval (-908974521 / 1000000000000) (-908974497 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks0_1 :
    compactCertificate536.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (728958160664837 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21046999150 / 1000000000000) (21046999151 / 1000000000000), orderedInterval (15978648473 / 1000000000000) (15978648475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (420864190287773 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27722031224 / 1000000000000) (-27721994534 / 1000000000000), orderedInterval (21040823505 / 1000000000000) (21040860195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (746830891126657 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24948176931 / 1000000000000) (-24948176745 / 1000000000000), orderedInterval (-7702272462 / 1000000000000) (-7702272275 / 1000000000000)))) (orderedInterval (-9340302443 / 1000000000000) (-9340299536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (697786294845733 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9127480799 / 1000000000000) (-9127480796 / 1000000000000), orderedInterval (25432831810 / 1000000000000) (25432831814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (497973225518389 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29992703985 / 1000000000000) (29992703993 / 1000000000000), orderedInterval (11074322883 / 1000000000000) (11074322891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (564648563267331 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7791119303 / 1000000000000) (7791119307 / 1000000000000), orderedInterval (-29010143364 / 1000000000000) (-29010143360 / 1000000000000)))) (orderedInterval (2961547668 / 1000000000000) (2961547718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (470745104480339 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32429364377 / 1000000000000) (-32429358449 / 1000000000000), orderedInterval (5525653457 / 1000000000000) (5525659384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (415917576075119 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25638714507 / 1000000000000) (-25638699651 / 1000000000000), orderedInterval (23839940321 / 1000000000000) (23839955177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (120549124712781 / 160000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6769026366 / 1000000000000) (6769026367 / 1000000000000), orderedInterval (28264576515 / 1000000000000) (28264576516 / 1000000000000)))) (orderedInterval (1266047778 / 1000000000000) (1266048736 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks0_2 :
    compactCertificate536.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (333445223108407 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9297237457 / 1000000000000) (9297237480 / 1000000000000), orderedInterval (-37970830370 / 1000000000000) (-37970830347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (282665208433727 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32807815319 / 1000000000000) (32807871871 / 1000000000000), orderedInterval (-26979859810 / 1000000000000) (-26979803257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (176878762871381 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49402659875 / 1000000000000) (49402669454 / 1000000000000), orderedInterval (-21057400359 / 1000000000000) (-21057390779 / 1000000000000)))) (orderedInterval (-1735165180 / 1000000000000) (-1735161561 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (95125986944427 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (22412417095 / 1000000000000) (22412417096 / 1000000000000), orderedInterval (69559404416 / 1000000000000) (69559404417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (258285559194281 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2570369111 / 1000000000000) (-2570369110 / 1000000000000), orderedInterval (-44326910256 / 1000000000000) (-44326910255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (352666849568137 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37044567673 / 1000000000000) (37044572593 / 1000000000000), orderedInterval (-8517056365 / 1000000000000) (-8517051445 / 1000000000000)))) (orderedInterval (-3194588502 / 1000000000000) (-3194588076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (149121237128619 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56453625497 / 1000000000000) (-56453623700 / 1000000000000), orderedInterval (15260743591 / 1000000000000) (15260745387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (606169549964299 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28422750384 / 1000000000000) (-28422750161 / 1000000000000), orderedInterval (-5667558538 / 1000000000000) (-5667558315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (404893167015941 / 800000000000) 0 (IntervalRat.scale (815 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31690853920 / 1000000000000) (-31690853919 / 1000000000000), orderedInterval (-15891686613 / 1000000000000) (-15891686612 / 1000000000000)))) (orderedInterval (7919386201 / 1000000000000) (7919386343 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks0 :
    compactCertificate536.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate536.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate536_chunkChecks0_0
    compactCertificate536_chunkChecks0_1 compactCertificate536_chunkChecks0_2

theorem compactCertificate536_chunkChecks1_0 :
    compactCertificate536.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (815 / 2) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4808321380 / 1000000000000) (-4808321376 / 1000000000000), orderedInterval (39237752859 / 1000000000000) (39237752863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (240130124507863 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27696689979 / 1000000000000) (-27696682238 / 1000000000000), orderedInterval (36840294105 / 1000000000000) (36840301847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (77653148481079 / 160000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26714958211 / 1000000000000) (26714977054 / 1000000000000), orderedInterval (-24482185820 / 1000000000000) (-24482166977 / 1000000000000)))) (orderedInterval (14094289998 / 1000000000000) (14094291402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (70069371438341 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33677355796 / 1000000000000) (33677355797 / 1000000000000), orderedInterval (78129964372 / 1000000000000) (78129964373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (188216187755777 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21951826948 / 1000000000000) (-21951826947 / 1000000000000), orderedInterval (-47112969523 / 1000000000000) (-47112969522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (511043563019709 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30377745970 / 1000000000000) (-30377723921 / 1000000000000), orderedInterval (8612886150 / 1000000000000) (8612908199 / 1000000000000)))) (orderedInterval (-2135171413 / 1000000000000) (-2135168900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (376432375511717 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3185192036 / 1000000000000) (3185192037 / 1000000000000), orderedInterval (36640982609 / 1000000000000) (36640982610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (645023291523641 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (8971177570 / 1000000000000) (8971177574 / 1000000000000), orderedInterval (-26634410473 / 1000000000000) (-26634410469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (475121237128619 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26161320451 / 1000000000000) (-26161320450 / 1000000000000), orderedInterval (-19663333424 / 1000000000000) (-19663333423 / 1000000000000)))) (orderedInterval (932838116 / 1000000000000) (932838157 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks1_1 :
    compactCertificate536.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (728958160664837 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21046999150 / 1000000000000) (21046999151 / 1000000000000), orderedInterval (15978648473 / 1000000000000) (15978648475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (420864190287773 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27722031224 / 1000000000000) (-27721994534 / 1000000000000), orderedInterval (21040823505 / 1000000000000) (21040860195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (746830891126657 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24948176931 / 1000000000000) (-24948176745 / 1000000000000), orderedInterval (-7702272462 / 1000000000000) (-7702272275 / 1000000000000)))) (orderedInterval (-6844426632 / 1000000000000) (-6844422726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (697786294845733 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9127480799 / 1000000000000) (-9127480796 / 1000000000000), orderedInterval (25432831810 / 1000000000000) (25432831814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (497973225518389 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29992703985 / 1000000000000) (29992703993 / 1000000000000), orderedInterval (11074322883 / 1000000000000) (11074322891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (564648563267331 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7791119303 / 1000000000000) (7791119307 / 1000000000000), orderedInterval (-29010143364 / 1000000000000) (-29010143360 / 1000000000000)))) (orderedInterval (871165471 / 1000000000000) (871165552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (470745104480339 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32429364377 / 1000000000000) (-32429358449 / 1000000000000), orderedInterval (5525653457 / 1000000000000) (5525659384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (415917576075119 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25638714507 / 1000000000000) (-25638699651 / 1000000000000), orderedInterval (23839940321 / 1000000000000) (23839955177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (120549124712781 / 160000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6769026366 / 1000000000000) (6769026367 / 1000000000000), orderedInterval (28264576515 / 1000000000000) (28264576516 / 1000000000000)))) (orderedInterval (-310408826 / 1000000000000) (-310407586 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks1_2 :
    compactCertificate536.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (333445223108407 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9297237457 / 1000000000000) (9297237480 / 1000000000000), orderedInterval (-37970830370 / 1000000000000) (-37970830347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (282665208433727 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32807815319 / 1000000000000) (32807871871 / 1000000000000), orderedInterval (-26979859810 / 1000000000000) (-26979803257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (176878762871381 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49402659875 / 1000000000000) (49402669454 / 1000000000000), orderedInterval (-21057400359 / 1000000000000) (-21057390779 / 1000000000000)))) (orderedInterval (7162020905 / 1000000000000) (7162023948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (95125986944427 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (22412417095 / 1000000000000) (22412417096 / 1000000000000), orderedInterval (69559404416 / 1000000000000) (69559404417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (258285559194281 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2570369111 / 1000000000000) (-2570369110 / 1000000000000), orderedInterval (-44326910256 / 1000000000000) (-44326910255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (352666849568137 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37044567673 / 1000000000000) (37044572593 / 1000000000000), orderedInterval (-8517056365 / 1000000000000) (-8517051445 / 1000000000000)))) (orderedInterval (1128094183 / 1000000000000) (1128094635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (149121237128619 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56453625497 / 1000000000000) (-56453623700 / 1000000000000), orderedInterval (15260743591 / 1000000000000) (15260745387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (606169549964299 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28422750384 / 1000000000000) (-28422750161 / 1000000000000), orderedInterval (-5667558538 / 1000000000000) (-5667558315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (404893167015941 / 800000000000) 1 (IntervalRat.scale (815 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31690853920 / 1000000000000) (-31690853919 / 1000000000000), orderedInterval (-15891686613 / 1000000000000) (-15891686612 / 1000000000000)))) (orderedInterval (4603206463 / 1000000000000) (4603206661 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks1 :
    compactCertificate536.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate536.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate536_chunkChecks1_0
    compactCertificate536_chunkChecks1_1 compactCertificate536_chunkChecks1_2

theorem compactCertificate536_chunkChecks2_0 :
    compactCertificate536.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (815 / 2) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4808321380 / 1000000000000) (-4808321376 / 1000000000000), orderedInterval (39237752859 / 1000000000000) (39237752863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (240130124507863 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27696689979 / 1000000000000) (-27696682238 / 1000000000000), orderedInterval (36840294105 / 1000000000000) (36840301847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (77653148481079 / 160000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26714958211 / 1000000000000) (26714977054 / 1000000000000), orderedInterval (-24482185820 / 1000000000000) (-24482166977 / 1000000000000)))) (orderedInterval (-212410614 / 1000000000000) (-212408965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (70069371438341 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33677355796 / 1000000000000) (33677355797 / 1000000000000), orderedInterval (78129964372 / 1000000000000) (78129964373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (188216187755777 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21951826948 / 1000000000000) (-21951826947 / 1000000000000), orderedInterval (-47112969523 / 1000000000000) (-47112969522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (511043563019709 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30377745970 / 1000000000000) (-30377723921 / 1000000000000), orderedInterval (8612886150 / 1000000000000) (8612908199 / 1000000000000)))) (orderedInterval (-5017633956 / 1000000000000) (-5017630021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (376432375511717 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3185192036 / 1000000000000) (3185192037 / 1000000000000), orderedInterval (36640982609 / 1000000000000) (36640982610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (645023291523641 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (8971177570 / 1000000000000) (8971177574 / 1000000000000), orderedInterval (-26634410473 / 1000000000000) (-26634410469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (475121237128619 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26161320451 / 1000000000000) (-26161320450 / 1000000000000), orderedInterval (-19663333424 / 1000000000000) (-19663333423 / 1000000000000)))) (orderedInterval (2423973854 / 1000000000000) (2423973925 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks2_1 :
    compactCertificate536.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (728958160664837 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21046999150 / 1000000000000) (21046999151 / 1000000000000), orderedInterval (15978648473 / 1000000000000) (15978648475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (420864190287773 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27722031224 / 1000000000000) (-27721994534 / 1000000000000), orderedInterval (21040823505 / 1000000000000) (21040860195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (746830891126657 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24948176931 / 1000000000000) (-24948176745 / 1000000000000), orderedInterval (-7702272462 / 1000000000000) (-7702272275 / 1000000000000)))) (orderedInterval (40751926288 / 1000000000000) (40751931684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (697786294845733 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9127480799 / 1000000000000) (-9127480796 / 1000000000000), orderedInterval (25432831810 / 1000000000000) (25432831814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (497973225518389 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29992703985 / 1000000000000) (29992703993 / 1000000000000), orderedInterval (11074322883 / 1000000000000) (11074322891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (564648563267331 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7791119303 / 1000000000000) (7791119307 / 1000000000000), orderedInterval (-29010143364 / 1000000000000) (-29010143360 / 1000000000000)))) (orderedInterval (-7256585348 / 1000000000000) (-7256585215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (470745104480339 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32429364377 / 1000000000000) (-32429358449 / 1000000000000), orderedInterval (5525653457 / 1000000000000) (5525659384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (415917576075119 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25638714507 / 1000000000000) (-25638699651 / 1000000000000), orderedInterval (23839940321 / 1000000000000) (23839955177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (120549124712781 / 160000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6769026366 / 1000000000000) (6769026367 / 1000000000000), orderedInterval (28264576515 / 1000000000000) (28264576516 / 1000000000000)))) (orderedInterval (-2199074049 / 1000000000000) (-2199072435 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks2_2 :
    compactCertificate536.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (333445223108407 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9297237457 / 1000000000000) (9297237480 / 1000000000000), orderedInterval (-37970830370 / 1000000000000) (-37970830347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (282665208433727 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32807815319 / 1000000000000) (32807871871 / 1000000000000), orderedInterval (-26979859810 / 1000000000000) (-26979803257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (176878762871381 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49402659875 / 1000000000000) (49402669454 / 1000000000000), orderedInterval (-21057400359 / 1000000000000) (-21057390779 / 1000000000000)))) (orderedInterval (2460249356 / 1000000000000) (2460251955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (95125986944427 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (22412417095 / 1000000000000) (22412417096 / 1000000000000), orderedInterval (69559404416 / 1000000000000) (69559404417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (258285559194281 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2570369111 / 1000000000000) (-2570369110 / 1000000000000), orderedInterval (-44326910256 / 1000000000000) (-44326910255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (352666849568137 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37044567673 / 1000000000000) (37044572593 / 1000000000000), orderedInterval (-8517056365 / 1000000000000) (-8517051445 / 1000000000000)))) (orderedInterval (3318385244 / 1000000000000) (3318385730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (149121237128619 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56453625497 / 1000000000000) (-56453623700 / 1000000000000), orderedInterval (15260743591 / 1000000000000) (15260745387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (606169549964299 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28422750384 / 1000000000000) (-28422750161 / 1000000000000), orderedInterval (-5667558538 / 1000000000000) (-5667558315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (404893167015941 / 800000000000) 2 (IntervalRat.scale (815 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31690853920 / 1000000000000) (-31690853919 / 1000000000000), orderedInterval (-15891686613 / 1000000000000) (-15891686612 / 1000000000000)))) (orderedInterval (-17111614397 / 1000000000000) (-17111614098 / 1000000000000))) = true
  rfl'

theorem compactCertificate536_chunkChecks2 :
    compactCertificate536.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate536.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate536_chunkChecks2_0
    compactCertificate536_chunkChecks2_1 compactCertificate536_chunkChecks2_2

theorem compactCertificate536_chunkChecks3_0 :
    compactCertificate536.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (815 / 2) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4808321380 / 1000000000000) (-4808321376 / 1000000000000), orderedInterval (39237752859 / 1000000000000) (39237752863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (240130124507863 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27696689979 / 1000000000000) (-27696682238 / 1000000000000), orderedInterval (36840294105 / 1000000000000) (36840301847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (77653148481079 / 160000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26714958211 / 1000000000000) (26714977054 / 1000000000000), orderedInterval (-24482185820 / 1000000000000) (-24482166977 / 1000000000000)))) (orderedInterval (-13261986874 / 1000000000000) (-13261984928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (70069371438341 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33677355796 / 1000000000000) (33677355797 / 1000000000000), orderedInterval (78129964372 / 1000000000000) (78129964373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (188216187755777 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21951826948 / 1000000000000) (-21951826947 / 1000000000000), orderedInterval (-47112969523 / 1000000000000) (-47112969522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (511043563019709 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30377745970 / 1000000000000) (-30377723921 / 1000000000000), orderedInterval (8612886150 / 1000000000000) (8612908199 / 1000000000000)))) (orderedInterval (2710483191 / 1000000000000) (2710489354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (376432375511717 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3185192036 / 1000000000000) (3185192037 / 1000000000000), orderedInterval (36640982609 / 1000000000000) (36640982610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (645023291523641 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (8971177570 / 1000000000000) (8971177574 / 1000000000000), orderedInterval (-26634410473 / 1000000000000) (-26634410469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (475121237128619 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26161320451 / 1000000000000) (-26161320450 / 1000000000000), orderedInterval (-19663333424 / 1000000000000) (-19663333423 / 1000000000000)))) (orderedInterval (-4898156543 / 1000000000000) (-4898156413 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate536_chunkChecks3_1 :
    compactCertificate536.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (728958160664837 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21046999150 / 1000000000000) (21046999151 / 1000000000000), orderedInterval (15978648473 / 1000000000000) (15978648475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (420864190287773 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27722031224 / 1000000000000) (-27721994534 / 1000000000000), orderedInterval (21040823505 / 1000000000000) (21040860195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (746830891126657 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24948176931 / 1000000000000) (-24948176745 / 1000000000000), orderedInterval (-7702272462 / 1000000000000) (-7702272275 / 1000000000000)))) (orderedInterval (41453281775 / 1000000000000) (41453289532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (697786294845733 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9127480799 / 1000000000000) (-9127480796 / 1000000000000), orderedInterval (25432831810 / 1000000000000) (25432831814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (497973225518389 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29992703985 / 1000000000000) (29992703993 / 1000000000000), orderedInterval (11074322883 / 1000000000000) (11074322891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (564648563267331 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7791119303 / 1000000000000) (7791119307 / 1000000000000), orderedInterval (-29010143364 / 1000000000000) (-29010143360 / 1000000000000)))) (orderedInterval (25020635 / 1000000000000) (25020860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (470745104480339 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32429364377 / 1000000000000) (-32429358449 / 1000000000000), orderedInterval (5525653457 / 1000000000000) (5525659384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (415917576075119 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25638714507 / 1000000000000) (-25638699651 / 1000000000000), orderedInterval (23839940321 / 1000000000000) (23839955177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (120549124712781 / 160000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6769026366 / 1000000000000) (6769026367 / 1000000000000), orderedInterval (28264576515 / 1000000000000) (28264576516 / 1000000000000)))) (orderedInterval (-1927587921 / 1000000000000) (-1927585816 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate536_chunkChecks3_2 :
    compactCertificate536.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (333445223108407 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9297237457 / 1000000000000) (9297237480 / 1000000000000), orderedInterval (-37970830370 / 1000000000000) (-37970830347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (282665208433727 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32807815319 / 1000000000000) (32807871871 / 1000000000000), orderedInterval (-26979859810 / 1000000000000) (-26979803257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (176878762871381 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49402659875 / 1000000000000) (49402669454 / 1000000000000), orderedInterval (-21057400359 / 1000000000000) (-21057390779 / 1000000000000)))) (orderedInterval (-7388737770 / 1000000000000) (-7388735535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (95125986944427 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (22412417095 / 1000000000000) (22412417096 / 1000000000000), orderedInterval (69559404416 / 1000000000000) (69559404417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (258285559194281 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2570369111 / 1000000000000) (-2570369110 / 1000000000000), orderedInterval (-44326910256 / 1000000000000) (-44326910255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (352666849568137 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37044567673 / 1000000000000) (37044572593 / 1000000000000), orderedInterval (-8517056365 / 1000000000000) (-8517051445 / 1000000000000)))) (orderedInterval (-1302742030 / 1000000000000) (-1302741506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (149121237128619 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56453625497 / 1000000000000) (-56453623700 / 1000000000000), orderedInterval (15260743591 / 1000000000000) (15260745387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (606169549964299 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28422750384 / 1000000000000) (-28422750161 / 1000000000000), orderedInterval (-5667558538 / 1000000000000) (-5667558315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (404893167015941 / 800000000000) 3 (IntervalRat.scale (815 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31690853920 / 1000000000000) (-31690853919 / 1000000000000), orderedInterval (-15891686613 / 1000000000000) (-15891686612 / 1000000000000)))) (orderedInterval (-8645292372 / 1000000000000) (-8645291893 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate536_chunkChecks3 :
    compactCertificate536.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate536.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate536_chunkChecks3_0
    compactCertificate536_chunkChecks3_1 compactCertificate536_chunkChecks3_2

theorem compactCertificate536_chunkChecks4_0 :
    compactCertificate536.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (815 / 2) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4808321380 / 1000000000000) (-4808321376 / 1000000000000), orderedInterval (39237752859 / 1000000000000) (39237752863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (240130124507863 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27696689979 / 1000000000000) (-27696682238 / 1000000000000), orderedInterval (36840294105 / 1000000000000) (36840301847 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (77653148481079 / 160000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26714958211 / 1000000000000) (26714977054 / 1000000000000), orderedInterval (-24482185820 / 1000000000000) (-24482166977 / 1000000000000)))) (orderedInterval (1237533420 / 1000000000000) (1237535727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (70069371438341 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (33677355796 / 1000000000000) (33677355797 / 1000000000000), orderedInterval (78129964372 / 1000000000000) (78129964373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (188216187755777 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-21951826948 / 1000000000000) (-21951826947 / 1000000000000), orderedInterval (-47112969523 / 1000000000000) (-47112969522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (511043563019709 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30377745970 / 1000000000000) (-30377723921 / 1000000000000), orderedInterval (8612886150 / 1000000000000) (8612908199 / 1000000000000)))) (orderedInterval (12938190138 / 1000000000000) (12938199811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (376432375511717 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3185192036 / 1000000000000) (3185192037 / 1000000000000), orderedInterval (36640982609 / 1000000000000) (36640982610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (645023291523641 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (8971177570 / 1000000000000) (8971177574 / 1000000000000), orderedInterval (-26634410473 / 1000000000000) (-26634410469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (475121237128619 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26161320451 / 1000000000000) (-26161320450 / 1000000000000), orderedInterval (-19663333424 / 1000000000000) (-19663333423 / 1000000000000)))) (orderedInterval (-7069428545 / 1000000000000) (-7069428305 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate536_chunkChecks4_1 :
    compactCertificate536.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (728958160664837 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21046999150 / 1000000000000) (21046999151 / 1000000000000), orderedInterval (15978648473 / 1000000000000) (15978648475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (420864190287773 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27722031224 / 1000000000000) (-27721994534 / 1000000000000), orderedInterval (21040823505 / 1000000000000) (21040860195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (746830891126657 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24948176931 / 1000000000000) (-24948176745 / 1000000000000), orderedInterval (-7702272462 / 1000000000000) (-7702272275 / 1000000000000)))) (orderedInterval (-197087394272 / 1000000000000) (-197087382467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (697786294845733 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9127480799 / 1000000000000) (-9127480796 / 1000000000000), orderedInterval (25432831810 / 1000000000000) (25432831814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (497973225518389 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29992703985 / 1000000000000) (29992703993 / 1000000000000), orderedInterval (11074322883 / 1000000000000) (11074322891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (564648563267331 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7791119303 / 1000000000000) (7791119307 / 1000000000000), orderedInterval (-29010143364 / 1000000000000) (-29010143360 / 1000000000000)))) (orderedInterval (18545267437 / 1000000000000) (18545267826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (470745104480339 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32429364377 / 1000000000000) (-32429358449 / 1000000000000), orderedInterval (5525653457 / 1000000000000) (5525659384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (415917576075119 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25638714507 / 1000000000000) (-25638699651 / 1000000000000), orderedInterval (23839940321 / 1000000000000) (23839955177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (120549124712781 / 160000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (6769026366 / 1000000000000) (6769026367 / 1000000000000), orderedInterval (28264576515 / 1000000000000) (28264576516 / 1000000000000)))) (orderedInterval (4293946373 / 1000000000000) (4293949138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate536_chunkChecks4_2 :
    compactCertificate536.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (333445223108407 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9297237457 / 1000000000000) (9297237480 / 1000000000000), orderedInterval (-37970830370 / 1000000000000) (-37970830347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (282665208433727 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32807815319 / 1000000000000) (32807871871 / 1000000000000), orderedInterval (-26979859810 / 1000000000000) (-26979803257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (176878762871381 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49402659875 / 1000000000000) (49402669454 / 1000000000000), orderedInterval (-21057400359 / 1000000000000) (-21057390779 / 1000000000000)))) (orderedInterval (-2500996818 / 1000000000000) (-2500994880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (95125986944427 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (22412417095 / 1000000000000) (22412417096 / 1000000000000), orderedInterval (69559404416 / 1000000000000) (69559404417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (258285559194281 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2570369111 / 1000000000000) (-2570369110 / 1000000000000), orderedInterval (-44326910256 / 1000000000000) (-44326910255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (352666849568137 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37044567673 / 1000000000000) (37044572593 / 1000000000000), orderedInterval (-8517056365 / 1000000000000) (-8517051445 / 1000000000000)))) (orderedInterval (-3861927714 / 1000000000000) (-3861927147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (149121237128619 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56453625497 / 1000000000000) (-56453623700 / 1000000000000), orderedInterval (15260743591 / 1000000000000) (15260745387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (606169549964299 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28422750384 / 1000000000000) (-28422750161 / 1000000000000), orderedInterval (-5667558538 / 1000000000000) (-5667558315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (404893167015941 / 800000000000) 4 (IntervalRat.scale (815 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31690853920 / 1000000000000) (-31690853919 / 1000000000000), orderedInterval (-15891686613 / 1000000000000) (-15891686612 / 1000000000000)))) (orderedInterval (41833288992 / 1000000000000) (41833289790 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate536_chunkChecks4 :
    compactCertificate536.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate536.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate536_chunkChecks4_0
    compactCertificate536_chunkChecks4_1 compactCertificate536_chunkChecks4_2

theorem compactCertificate536_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate536.chunkCheck r b = true :=
  compactCertificate536.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate536_chunkChecks0
    · exact compactCertificate536_chunkChecks1
    · exact compactCertificate536_chunkChecks2
    · exact compactCertificate536_chunkChecks3
    · exact compactCertificate536_chunkChecks4)

theorem compactCertificate536_coefficient0 :
    compactCertificate536.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate536_coefficient1 :
    compactCertificate536.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate536_coefficient2 :
    compactCertificate536.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate536_coefficient3 :
    compactCertificate536.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate536_coefficient4 :
    compactCertificate536.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate536_coefficients : ∀ r : Fin 5,
    compactCertificate536.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate536_coefficient0
  · exact compactCertificate536_coefficient1
  · exact compactCertificate536_coefficient2
  · exact compactCertificate536_coefficient3
  · exact compactCertificate536_coefficient4

theorem compactCertificate536_lower : (1 : ℚ) ≤ compactCertificate536.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate536, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate536_proves {t : ℝ} (ht : t ∈ compactCertificate536.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate536.proves compactCertificate536_states compactCertificate536_chunks
    compactCertificate536_coefficients compactCertificate536_lower ht

end Erdos232
