/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate474 : CompactCertificate where
  left := 345
  right := 346
  center := 691 / 2
  grid := fun i =>
    match i.val with
    | 0 => 110
    | 1 => 81
    | 2 => 131
    | 3 => 24
    | 4 => 64
    | 5 => 172
    | 6 => 127
    | 7 => 218
    | 8 => 160
    | 9 => 246
    | 10 => 142
    | 11 => 252
    | 12 => 236
    | 13 => 168
    | 14 => 191
    | 15 => 159
    | 16 => 140
    | 17 => 203
    | 18 => 113
    | 19 => 95
    | 20 => 60
    | 21 => 32
    | 22 => 87
    | 23 => 119
    | 24 => 50
    | 25 => 205
    | _ => 137
  point := fun i =>
    match i.val with
    | 0 => 691 / 2
    | 1 => 1017974944999591 / 4000000000000
    | 2 => 329192181597703 / 800000000000
    | 3 => 297042550085237 / 4000000000000
    | 4 => 797898072019889 / 4000000000000
    | 5 => 2166448478813613 / 4000000000000
    | 6 => 1595796144040469 / 4000000000000
    | 7 => 2734423892287337 / 4000000000000
    | 8 => 2014164262919483 / 4000000000000
    | 9 => 3090245944904309 / 4000000000000
    | 10 => 1784154328152461 / 4000000000000
    | 11 => 3166013164224049 / 4000000000000
    | 12 => 2958100182444181 / 4000000000000
    | 13 => 2111039870142373 / 4000000000000
    | 14 => 2393694216059667 / 4000000000000
    | 15 => 1995612682183523 / 4000000000000
    | 16 => 1763184325569983 / 4000000000000
    | 17 => 511039540960317 / 800000000000
    | 18 => 1413562264833799 / 4000000000000
    | 19 => 1198292386673039 / 4000000000000
    | 20 => 749835737080517 / 4000000000000
    | 21 => 403264153242939 / 4000000000000
    | 22 => 1094940622105817 / 4000000000000
    | 23 => 1495047810132409 / 4000000000000
    | 24 => 632164262919483 / 4000000000000
    | 25 => 2569712632057243 / 4000000000000
    | _ => 1716448947288437 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (27975256112 / 1000000000000) (27975256113 / 1000000000000), orderedInterval (32516996345 / 1000000000000) (32516996346 / 1000000000000))
    | 1 => (orderedInterval (-36212815927 / 1000000000000) (-36212815926 / 1000000000000), orderedInterval (-34427349594 / 1000000000000) (-34427349593 / 1000000000000))
    | 2 => (orderedInterval (-26132825226 / 1000000000000) (-26132825225 / 1000000000000), orderedInterval (-29365243607 / 1000000000000) (-29365243606 / 1000000000000))
    | 3 => (orderedInterval (-32084753149 / 1000000000000) (-32084752047 / 1000000000000), orderedInterval (87069294672 / 1000000000000) (87069295773 / 1000000000000))
    | 4 => (orderedInterval (-40629498509 / 1000000000000) (-40629443424 / 1000000000000), orderedInterval (39353943851 / 1000000000000) (39353998936 / 1000000000000))
    | 5 => (orderedInterval (30527026694 / 1000000000000) (30527109025 / 1000000000000), orderedInterval (-15633162657 / 1000000000000) (-15633080326 / 1000000000000))
    | 6 => (orderedInterval (-27283374603 / 1000000000000) (-27283374602 / 1000000000000), orderedInterval (-29143874024 / 1000000000000) (-29143874023 / 1000000000000))
    | 7 => (orderedInterval (-13983849765 / 1000000000000) (-13983849664 / 1000000000000), orderedInterval (27134372566 / 1000000000000) (27134372667 / 1000000000000))
    | 8 => (orderedInterval (35377032523 / 1000000000000) (35377034309 / 1000000000000), orderedInterval (-3605927503 / 1000000000000) (-3605925716 / 1000000000000))
    | 9 => (orderedInterval (14136978058 / 1000000000000) (14136978059 / 1000000000000), orderedInterval (24974517591 / 1000000000000) (24974517592 / 1000000000000))
    | 10 => (orderedInterval (24841223847 / 1000000000000) (24841223848 / 1000000000000), orderedInterval (28435969916 / 1000000000000) (28435969917 / 1000000000000))
    | 11 => (orderedInterval (16181242207 / 1000000000000) (16181242208 / 1000000000000), orderedInterval (23281079851 / 1000000000000) (23281079852 / 1000000000000))
    | 12 => (orderedInterval (-26222272748 / 1000000000000) (-26222201634 / 1000000000000), orderedInterval (13179897308 / 1000000000000) (13179968421 / 1000000000000))
    | 13 => (orderedInterval (23865755918 / 1000000000000) (23865755919 / 1000000000000), orderedInterval (25210173190 / 1000000000000) (25210173191 / 1000000000000))
    | 14 => (orderedInterval (24188322691 / 1000000000000) (24188334146 / 1000000000000), orderedInterval (-21900635910 / 1000000000000) (-21900624454 / 1000000000000))
    | 15 => (orderedInterval (-6222467928 / 1000000000000) (-6222467927 / 1000000000000), orderedInterval (-35169326872 / 1000000000000) (-35169326871 / 1000000000000))
    | 16 => (orderedInterval (37337713693 / 1000000000000) (37337716987 / 1000000000000), orderedInterval (-7123612305 / 1000000000000) (-7123609010 / 1000000000000))
    | 17 => (orderedInterval (-30420663521 / 1000000000000) (-30420642491 / 1000000000000), orderedInterval (8460119326 / 1000000000000) (8460140356 / 1000000000000))
    | 18 => (orderedInterval (31158384338 / 1000000000000) (31158417749 / 1000000000000), orderedInterval (-28864513035 / 1000000000000) (-28864479624 / 1000000000000))
    | 19 => (orderedInterval (-43521197903 / 1000000000000) (-43521190490 / 1000000000000), orderedInterval (15271097181 / 1000000000000) (15271104594 / 1000000000000))
    | 20 => (orderedInterval (-14524489663 / 1000000000000) (-14524489516 / 1000000000000), orderedInterval (56475421677 / 1000000000000) (56475421824 / 1000000000000))
    | 21 => (orderedInterval (69676874995 / 1000000000000) (69676874996 / 1000000000000), orderedInterval (37861236116 / 1000000000000) (37861236117 / 1000000000000))
    | 22 => (orderedInterval (-44974601430 / 1000000000000) (-44974601429 / 1000000000000), orderedInterval (-17323600927 / 1000000000000) (-17323600925 / 1000000000000))
    | 23 => (orderedInterval (-26508046667 / 1000000000000) (-26508046666 / 1000000000000), orderedInterval (-31596797025 / 1000000000000) (-31596797024 / 1000000000000))
    | 24 => (orderedInterval (62495808888 / 1000000000000) (62495809431 / 1000000000000), orderedInterval (-11263295822 / 1000000000000) (-11263295280 / 1000000000000))
    | 25 => (orderedInterval (22868064933 / 1000000000000) (22868072251 / 1000000000000), orderedInterval (-21651343250 / 1000000000000) (-21651335931 / 1000000000000))
    | _ => (orderedInterval (18494838696 / 1000000000000) (18494839450 / 1000000000000), orderedInterval (-33807871718 / 1000000000000) (-33807870964 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9217475014 / 1000000000000) (9217475038 / 1000000000000)
      | 1 => orderedInterval (-3305518360 / 1000000000000) (-3305510442 / 1000000000000)
      | 2 => orderedInterval (1286310940 / 1000000000000) (1286311006 / 1000000000000)
      | 3 => orderedInterval (1628818808 / 1000000000000) (1628818946 / 1000000000000)
      | 4 => orderedInterval (2607799016 / 1000000000000) (2607800400 / 1000000000000)
      | 5 => orderedInterval (-2987457641 / 1000000000000) (-2987456880 / 1000000000000)
      | 6 => orderedInterval (-2991546777 / 1000000000000) (-2991540923 / 1000000000000)
      | 7 => orderedInterval (1765287649 / 1000000000000) (1765287690 / 1000000000000)
      | _ => orderedInterval (-4954879025 / 1000000000000) (-4954878188 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (10599988923 / 1000000000000) (10599988951 / 1000000000000)
      | 1 => orderedInterval (2368718567 / 1000000000000) (2368728954 / 1000000000000)
      | 2 => orderedInterval (-1782966183 / 1000000000000) (-1782966080 / 1000000000000)
      | 3 => orderedInterval (378832637 / 1000000000000) (378832922 / 1000000000000)
      | 4 => orderedInterval (3324204325 / 1000000000000) (3324207240 / 1000000000000)
      | 5 => orderedInterval (334155170 / 1000000000000) (334156455 / 1000000000000)
      | 6 => orderedInterval (4968726840 / 1000000000000) (4968732751 / 1000000000000)
      | 7 => orderedInterval (2727009351 / 1000000000000) (2727009389 / 1000000000000)
      | _ => orderedInterval (11124425406 / 1000000000000) (11124426825 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8760766882 / 1000000000000) (-8760766850 / 1000000000000)
      | 1 => orderedInterval (5804545320 / 1000000000000) (5804560470 / 1000000000000)
      | 2 => orderedInterval (-3499471661 / 1000000000000) (-3499471497 / 1000000000000)
      | 3 => orderedInterval (-2580985896 / 1000000000000) (-2580985285 / 1000000000000)
      | 4 => orderedInterval (-7077160606 / 1000000000000) (-7077154431 / 1000000000000)
      | 5 => orderedInterval (6289443521 / 1000000000000) (6289445744 / 1000000000000)
      | 6 => orderedInterval (3485027501 / 1000000000000) (3485033501 / 1000000000000)
      | 7 => orderedInterval (-2916328939 / 1000000000000) (-2916328901 / 1000000000000)
      | _ => orderedInterval (11677892955 / 1000000000000) (11677895436 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9823781826 / 1000000000000) (-9823781788 / 1000000000000)
      | 1 => orderedInterval (-4565214026 / 1000000000000) (-4565190951 / 1000000000000)
      | 2 => orderedInterval (6762717970 / 1000000000000) (6762718237 / 1000000000000)
      | 3 => orderedInterval (5298129905 / 1000000000000) (5298131242 / 1000000000000)
      | 4 => orderedInterval (-6718959413 / 1000000000000) (-6718946317 / 1000000000000)
      | 5 => orderedInterval (-1011055431 / 1000000000000) (-1011051519 / 1000000000000)
      | 6 => orderedInterval (-4678971047 / 1000000000000) (-4678964965 / 1000000000000)
      | 7 => orderedInterval (-3235353145 / 1000000000000) (-3235353106 / 1000000000000)
      | _ => orderedInterval (-23510606787 / 1000000000000) (-23510602372 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (7960332889 / 1000000000000) (7960332932 / 1000000000000)
      | 1 => orderedInterval (-13243100969 / 1000000000000) (-13243065117 / 1000000000000)
      | 2 => orderedInterval (10428772793 / 1000000000000) (10428773239 / 1000000000000)
      | 3 => orderedInterval (5639752241 / 1000000000000) (5639755210 / 1000000000000)
      | 4 => orderedInterval (21160921238 / 1000000000000) (21160949108 / 1000000000000)
      | 5 => orderedInterval (-15069760615 / 1000000000000) (-15069753628 / 1000000000000)
      | 6 => orderedInterval (-4074496981 / 1000000000000) (-4074490788 / 1000000000000)
      | 7 => orderedInterval (3193789444 / 1000000000000) (3193789484 / 1000000000000)
      | _ => orderedInterval (-30356600054 / 1000000000000) (-30356592081 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2266289624 / 1000000000000) (2266306647 / 1000000000000)
    | 1 => orderedInterval (34043095036 / 1000000000000) (34043117407 / 1000000000000)
    | 2 => orderedInterval (2422195313 / 1000000000000) (2422228187 / 1000000000000)
    | 3 => orderedInterval (-41483093800 / 1000000000000) (-41483041539 / 1000000000000)
    | _ => orderedInterval (-14360390014 / 1000000000000) (-14360301641 / 1000000000000)

theorem compactCertificate474_stateChecks0 :
    compactCertificate474.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (691 / 2)) (orderedInterval (27975256112 / 1000000000000) (27975256113 / 1000000000000), orderedInterval (32516996345 / 1000000000000) (32516996346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1017974944999591 / 4000000000000)) (orderedInterval (-36212815927 / 1000000000000) (-36212815926 / 1000000000000), orderedInterval (-34427349594 / 1000000000000) (-34427349593 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (329192181597703 / 800000000000)) (orderedInterval (-26132825226 / 1000000000000) (-26132825225 / 1000000000000), orderedInterval (-29365243607 / 1000000000000) (-29365243606 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks1 :
    compactCertificate474.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (297042550085237 / 4000000000000)) (orderedInterval (-32084753149 / 1000000000000) (-32084752047 / 1000000000000), orderedInterval (87069294672 / 1000000000000) (87069295773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (797898072019889 / 4000000000000)) (orderedInterval (-40629498509 / 1000000000000) (-40629443424 / 1000000000000), orderedInterval (39353943851 / 1000000000000) (39353998936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2166448478813613 / 4000000000000)) (orderedInterval (30527026694 / 1000000000000) (30527109025 / 1000000000000), orderedInterval (-15633162657 / 1000000000000) (-15633080326 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks2 :
    compactCertificate474.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1595796144040469 / 4000000000000)) (orderedInterval (-27283374603 / 1000000000000) (-27283374602 / 1000000000000), orderedInterval (-29143874024 / 1000000000000) (-29143874023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2734423892287337 / 4000000000000)) (orderedInterval (-13983849765 / 1000000000000) (-13983849664 / 1000000000000), orderedInterval (27134372566 / 1000000000000) (27134372667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2014164262919483 / 4000000000000)) (orderedInterval (35377032523 / 1000000000000) (35377034309 / 1000000000000), orderedInterval (-3605927503 / 1000000000000) (-3605925716 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks3 :
    compactCertificate474.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3090245944904309 / 4000000000000)) (orderedInterval (14136978058 / 1000000000000) (14136978059 / 1000000000000), orderedInterval (24974517591 / 1000000000000) (24974517592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1784154328152461 / 4000000000000)) (orderedInterval (24841223847 / 1000000000000) (24841223848 / 1000000000000), orderedInterval (28435969916 / 1000000000000) (28435969917 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3166013164224049 / 4000000000000)) (orderedInterval (16181242207 / 1000000000000) (16181242208 / 1000000000000), orderedInterval (23281079851 / 1000000000000) (23281079852 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks4 :
    compactCertificate474.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2958100182444181 / 4000000000000)) (orderedInterval (-26222272748 / 1000000000000) (-26222201634 / 1000000000000), orderedInterval (13179897308 / 1000000000000) (13179968421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2111039870142373 / 4000000000000)) (orderedInterval (23865755918 / 1000000000000) (23865755919 / 1000000000000), orderedInterval (25210173190 / 1000000000000) (25210173191 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2393694216059667 / 4000000000000)) (orderedInterval (24188322691 / 1000000000000) (24188334146 / 1000000000000), orderedInterval (-21900635910 / 1000000000000) (-21900624454 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks5 :
    compactCertificate474.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1995612682183523 / 4000000000000)) (orderedInterval (-6222467928 / 1000000000000) (-6222467927 / 1000000000000), orderedInterval (-35169326872 / 1000000000000) (-35169326871 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1763184325569983 / 4000000000000)) (orderedInterval (37337713693 / 1000000000000) (37337716987 / 1000000000000), orderedInterval (-7123612305 / 1000000000000) (-7123609010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (511039540960317 / 800000000000)) (orderedInterval (-30420663521 / 1000000000000) (-30420642491 / 1000000000000), orderedInterval (8460119326 / 1000000000000) (8460140356 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks6 :
    compactCertificate474.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1413562264833799 / 4000000000000)) (orderedInterval (31158384338 / 1000000000000) (31158417749 / 1000000000000), orderedInterval (-28864513035 / 1000000000000) (-28864479624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1198292386673039 / 4000000000000)) (orderedInterval (-43521197903 / 1000000000000) (-43521190490 / 1000000000000), orderedInterval (15271097181 / 1000000000000) (15271104594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (749835737080517 / 4000000000000)) (orderedInterval (-14524489663 / 1000000000000) (-14524489516 / 1000000000000), orderedInterval (56475421677 / 1000000000000) (56475421824 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks7 :
    compactCertificate474.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (403264153242939 / 4000000000000)) (orderedInterval (69676874995 / 1000000000000) (69676874996 / 1000000000000), orderedInterval (37861236116 / 1000000000000) (37861236117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1094940622105817 / 4000000000000)) (orderedInterval (-44974601430 / 1000000000000) (-44974601429 / 1000000000000), orderedInterval (-17323600927 / 1000000000000) (-17323600925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1495047810132409 / 4000000000000)) (orderedInterval (-26508046667 / 1000000000000) (-26508046666 / 1000000000000), orderedInterval (-31596797025 / 1000000000000) (-31596797024 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_stateChecks8 :
    compactCertificate474.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (632164262919483 / 4000000000000)) (orderedInterval (62495808888 / 1000000000000) (62495809431 / 1000000000000), orderedInterval (-11263295822 / 1000000000000) (-11263295280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2569712632057243 / 4000000000000)) (orderedInterval (22868064933 / 1000000000000) (22868072251 / 1000000000000), orderedInterval (-21651343250 / 1000000000000) (-21651335931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1716448947288437 / 4000000000000)) (orderedInterval (18494838696 / 1000000000000) (18494839450 / 1000000000000), orderedInterval (-33807871718 / 1000000000000) (-33807870964 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_states : ∀ j,
    BesselStateValid (compactCertificate474.point j) (compactCertificate474.state j) :=
  compactCertificate474.statesValid_of_checks3 compactCertificate474_stateChecks0
    compactCertificate474_stateChecks1 compactCertificate474_stateChecks2
    compactCertificate474_stateChecks3 compactCertificate474_stateChecks4
    compactCertificate474_stateChecks5 compactCertificate474_stateChecks6
    compactCertificate474_stateChecks7 compactCertificate474_stateChecks8

theorem compactCertificate474_chunkChecks0_0 :
    compactCertificate474.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (691 / 2) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27975256112 / 1000000000000) (27975256113 / 1000000000000), orderedInterval (32516996345 / 1000000000000) (32516996346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1017974944999591 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36212815927 / 1000000000000) (-36212815926 / 1000000000000), orderedInterval (-34427349594 / 1000000000000) (-34427349593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (329192181597703 / 800000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26132825226 / 1000000000000) (-26132825225 / 1000000000000), orderedInterval (-29365243607 / 1000000000000) (-29365243606 / 1000000000000)))) (orderedInterval (9217475014 / 1000000000000) (9217475038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (297042550085237 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32084753149 / 1000000000000) (-32084752047 / 1000000000000), orderedInterval (87069294672 / 1000000000000) (87069295773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (797898072019889 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40629498509 / 1000000000000) (-40629443424 / 1000000000000), orderedInterval (39353943851 / 1000000000000) (39353998936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2166448478813613 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30527026694 / 1000000000000) (30527109025 / 1000000000000), orderedInterval (-15633162657 / 1000000000000) (-15633080326 / 1000000000000)))) (orderedInterval (-3305518360 / 1000000000000) (-3305510442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1595796144040469 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27283374603 / 1000000000000) (-27283374602 / 1000000000000), orderedInterval (-29143874024 / 1000000000000) (-29143874023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2734423892287337 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13983849765 / 1000000000000) (-13983849664 / 1000000000000), orderedInterval (27134372566 / 1000000000000) (27134372667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2014164262919483 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35377032523 / 1000000000000) (35377034309 / 1000000000000), orderedInterval (-3605927503 / 1000000000000) (-3605925716 / 1000000000000)))) (orderedInterval (1286310940 / 1000000000000) (1286311006 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks0_1 :
    compactCertificate474.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3090245944904309 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14136978058 / 1000000000000) (14136978059 / 1000000000000), orderedInterval (24974517591 / 1000000000000) (24974517592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1784154328152461 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24841223847 / 1000000000000) (24841223848 / 1000000000000), orderedInterval (28435969916 / 1000000000000) (28435969917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3166013164224049 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16181242207 / 1000000000000) (16181242208 / 1000000000000), orderedInterval (23281079851 / 1000000000000) (23281079852 / 1000000000000)))) (orderedInterval (1628818808 / 1000000000000) (1628818946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2958100182444181 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26222272748 / 1000000000000) (-26222201634 / 1000000000000), orderedInterval (13179897308 / 1000000000000) (13179968421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2111039870142373 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23865755918 / 1000000000000) (23865755919 / 1000000000000), orderedInterval (25210173190 / 1000000000000) (25210173191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2393694216059667 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24188322691 / 1000000000000) (24188334146 / 1000000000000), orderedInterval (-21900635910 / 1000000000000) (-21900624454 / 1000000000000)))) (orderedInterval (2607799016 / 1000000000000) (2607800400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1995612682183523 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6222467928 / 1000000000000) (-6222467927 / 1000000000000), orderedInterval (-35169326872 / 1000000000000) (-35169326871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1763184325569983 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37337713693 / 1000000000000) (37337716987 / 1000000000000), orderedInterval (-7123612305 / 1000000000000) (-7123609010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (511039540960317 / 800000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30420663521 / 1000000000000) (-30420642491 / 1000000000000), orderedInterval (8460119326 / 1000000000000) (8460140356 / 1000000000000)))) (orderedInterval (-2987457641 / 1000000000000) (-2987456880 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks0_2 :
    compactCertificate474.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1413562264833799 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31158384338 / 1000000000000) (31158417749 / 1000000000000), orderedInterval (-28864513035 / 1000000000000) (-28864479624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1198292386673039 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43521197903 / 1000000000000) (-43521190490 / 1000000000000), orderedInterval (15271097181 / 1000000000000) (15271104594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (749835737080517 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14524489663 / 1000000000000) (-14524489516 / 1000000000000), orderedInterval (56475421677 / 1000000000000) (56475421824 / 1000000000000)))) (orderedInterval (-2991546777 / 1000000000000) (-2991540923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (403264153242939 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69676874995 / 1000000000000) (69676874996 / 1000000000000), orderedInterval (37861236116 / 1000000000000) (37861236117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1094940622105817 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44974601430 / 1000000000000) (-44974601429 / 1000000000000), orderedInterval (-17323600927 / 1000000000000) (-17323600925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1495047810132409 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26508046667 / 1000000000000) (-26508046666 / 1000000000000), orderedInterval (-31596797025 / 1000000000000) (-31596797024 / 1000000000000)))) (orderedInterval (1765287649 / 1000000000000) (1765287690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (632164262919483 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62495808888 / 1000000000000) (62495809431 / 1000000000000), orderedInterval (-11263295822 / 1000000000000) (-11263295280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2569712632057243 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22868064933 / 1000000000000) (22868072251 / 1000000000000), orderedInterval (-21651343250 / 1000000000000) (-21651335931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1716448947288437 / 4000000000000) 0 (IntervalRat.scale (691 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18494838696 / 1000000000000) (18494839450 / 1000000000000), orderedInterval (-33807871718 / 1000000000000) (-33807870964 / 1000000000000)))) (orderedInterval (-4954879025 / 1000000000000) (-4954878188 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks0 :
    compactCertificate474.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate474.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate474_chunkChecks0_0
    compactCertificate474_chunkChecks0_1 compactCertificate474_chunkChecks0_2

theorem compactCertificate474_chunkChecks1_0 :
    compactCertificate474.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (691 / 2) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27975256112 / 1000000000000) (27975256113 / 1000000000000), orderedInterval (32516996345 / 1000000000000) (32516996346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1017974944999591 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36212815927 / 1000000000000) (-36212815926 / 1000000000000), orderedInterval (-34427349594 / 1000000000000) (-34427349593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (329192181597703 / 800000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26132825226 / 1000000000000) (-26132825225 / 1000000000000), orderedInterval (-29365243607 / 1000000000000) (-29365243606 / 1000000000000)))) (orderedInterval (10599988923 / 1000000000000) (10599988951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (297042550085237 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32084753149 / 1000000000000) (-32084752047 / 1000000000000), orderedInterval (87069294672 / 1000000000000) (87069295773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (797898072019889 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40629498509 / 1000000000000) (-40629443424 / 1000000000000), orderedInterval (39353943851 / 1000000000000) (39353998936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2166448478813613 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30527026694 / 1000000000000) (30527109025 / 1000000000000), orderedInterval (-15633162657 / 1000000000000) (-15633080326 / 1000000000000)))) (orderedInterval (2368718567 / 1000000000000) (2368728954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1595796144040469 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27283374603 / 1000000000000) (-27283374602 / 1000000000000), orderedInterval (-29143874024 / 1000000000000) (-29143874023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2734423892287337 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13983849765 / 1000000000000) (-13983849664 / 1000000000000), orderedInterval (27134372566 / 1000000000000) (27134372667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2014164262919483 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35377032523 / 1000000000000) (35377034309 / 1000000000000), orderedInterval (-3605927503 / 1000000000000) (-3605925716 / 1000000000000)))) (orderedInterval (-1782966183 / 1000000000000) (-1782966080 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks1_1 :
    compactCertificate474.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3090245944904309 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14136978058 / 1000000000000) (14136978059 / 1000000000000), orderedInterval (24974517591 / 1000000000000) (24974517592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1784154328152461 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24841223847 / 1000000000000) (24841223848 / 1000000000000), orderedInterval (28435969916 / 1000000000000) (28435969917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3166013164224049 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16181242207 / 1000000000000) (16181242208 / 1000000000000), orderedInterval (23281079851 / 1000000000000) (23281079852 / 1000000000000)))) (orderedInterval (378832637 / 1000000000000) (378832922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2958100182444181 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26222272748 / 1000000000000) (-26222201634 / 1000000000000), orderedInterval (13179897308 / 1000000000000) (13179968421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2111039870142373 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23865755918 / 1000000000000) (23865755919 / 1000000000000), orderedInterval (25210173190 / 1000000000000) (25210173191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2393694216059667 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24188322691 / 1000000000000) (24188334146 / 1000000000000), orderedInterval (-21900635910 / 1000000000000) (-21900624454 / 1000000000000)))) (orderedInterval (3324204325 / 1000000000000) (3324207240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1995612682183523 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6222467928 / 1000000000000) (-6222467927 / 1000000000000), orderedInterval (-35169326872 / 1000000000000) (-35169326871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1763184325569983 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37337713693 / 1000000000000) (37337716987 / 1000000000000), orderedInterval (-7123612305 / 1000000000000) (-7123609010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (511039540960317 / 800000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30420663521 / 1000000000000) (-30420642491 / 1000000000000), orderedInterval (8460119326 / 1000000000000) (8460140356 / 1000000000000)))) (orderedInterval (334155170 / 1000000000000) (334156455 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks1_2 :
    compactCertificate474.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1413562264833799 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31158384338 / 1000000000000) (31158417749 / 1000000000000), orderedInterval (-28864513035 / 1000000000000) (-28864479624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1198292386673039 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43521197903 / 1000000000000) (-43521190490 / 1000000000000), orderedInterval (15271097181 / 1000000000000) (15271104594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (749835737080517 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14524489663 / 1000000000000) (-14524489516 / 1000000000000), orderedInterval (56475421677 / 1000000000000) (56475421824 / 1000000000000)))) (orderedInterval (4968726840 / 1000000000000) (4968732751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (403264153242939 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69676874995 / 1000000000000) (69676874996 / 1000000000000), orderedInterval (37861236116 / 1000000000000) (37861236117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1094940622105817 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44974601430 / 1000000000000) (-44974601429 / 1000000000000), orderedInterval (-17323600927 / 1000000000000) (-17323600925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1495047810132409 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26508046667 / 1000000000000) (-26508046666 / 1000000000000), orderedInterval (-31596797025 / 1000000000000) (-31596797024 / 1000000000000)))) (orderedInterval (2727009351 / 1000000000000) (2727009389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (632164262919483 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62495808888 / 1000000000000) (62495809431 / 1000000000000), orderedInterval (-11263295822 / 1000000000000) (-11263295280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2569712632057243 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22868064933 / 1000000000000) (22868072251 / 1000000000000), orderedInterval (-21651343250 / 1000000000000) (-21651335931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1716448947288437 / 4000000000000) 1 (IntervalRat.scale (691 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18494838696 / 1000000000000) (18494839450 / 1000000000000), orderedInterval (-33807871718 / 1000000000000) (-33807870964 / 1000000000000)))) (orderedInterval (11124425406 / 1000000000000) (11124426825 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks1 :
    compactCertificate474.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate474.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate474_chunkChecks1_0
    compactCertificate474_chunkChecks1_1 compactCertificate474_chunkChecks1_2

theorem compactCertificate474_chunkChecks2_0 :
    compactCertificate474.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (691 / 2) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27975256112 / 1000000000000) (27975256113 / 1000000000000), orderedInterval (32516996345 / 1000000000000) (32516996346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1017974944999591 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36212815927 / 1000000000000) (-36212815926 / 1000000000000), orderedInterval (-34427349594 / 1000000000000) (-34427349593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (329192181597703 / 800000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26132825226 / 1000000000000) (-26132825225 / 1000000000000), orderedInterval (-29365243607 / 1000000000000) (-29365243606 / 1000000000000)))) (orderedInterval (-8760766882 / 1000000000000) (-8760766850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (297042550085237 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32084753149 / 1000000000000) (-32084752047 / 1000000000000), orderedInterval (87069294672 / 1000000000000) (87069295773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (797898072019889 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40629498509 / 1000000000000) (-40629443424 / 1000000000000), orderedInterval (39353943851 / 1000000000000) (39353998936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2166448478813613 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30527026694 / 1000000000000) (30527109025 / 1000000000000), orderedInterval (-15633162657 / 1000000000000) (-15633080326 / 1000000000000)))) (orderedInterval (5804545320 / 1000000000000) (5804560470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1595796144040469 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27283374603 / 1000000000000) (-27283374602 / 1000000000000), orderedInterval (-29143874024 / 1000000000000) (-29143874023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2734423892287337 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13983849765 / 1000000000000) (-13983849664 / 1000000000000), orderedInterval (27134372566 / 1000000000000) (27134372667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2014164262919483 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35377032523 / 1000000000000) (35377034309 / 1000000000000), orderedInterval (-3605927503 / 1000000000000) (-3605925716 / 1000000000000)))) (orderedInterval (-3499471661 / 1000000000000) (-3499471497 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks2_1 :
    compactCertificate474.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3090245944904309 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14136978058 / 1000000000000) (14136978059 / 1000000000000), orderedInterval (24974517591 / 1000000000000) (24974517592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1784154328152461 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24841223847 / 1000000000000) (24841223848 / 1000000000000), orderedInterval (28435969916 / 1000000000000) (28435969917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3166013164224049 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16181242207 / 1000000000000) (16181242208 / 1000000000000), orderedInterval (23281079851 / 1000000000000) (23281079852 / 1000000000000)))) (orderedInterval (-2580985896 / 1000000000000) (-2580985285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2958100182444181 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26222272748 / 1000000000000) (-26222201634 / 1000000000000), orderedInterval (13179897308 / 1000000000000) (13179968421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2111039870142373 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23865755918 / 1000000000000) (23865755919 / 1000000000000), orderedInterval (25210173190 / 1000000000000) (25210173191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2393694216059667 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24188322691 / 1000000000000) (24188334146 / 1000000000000), orderedInterval (-21900635910 / 1000000000000) (-21900624454 / 1000000000000)))) (orderedInterval (-7077160606 / 1000000000000) (-7077154431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1995612682183523 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6222467928 / 1000000000000) (-6222467927 / 1000000000000), orderedInterval (-35169326872 / 1000000000000) (-35169326871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1763184325569983 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37337713693 / 1000000000000) (37337716987 / 1000000000000), orderedInterval (-7123612305 / 1000000000000) (-7123609010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (511039540960317 / 800000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30420663521 / 1000000000000) (-30420642491 / 1000000000000), orderedInterval (8460119326 / 1000000000000) (8460140356 / 1000000000000)))) (orderedInterval (6289443521 / 1000000000000) (6289445744 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks2_2 :
    compactCertificate474.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1413562264833799 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31158384338 / 1000000000000) (31158417749 / 1000000000000), orderedInterval (-28864513035 / 1000000000000) (-28864479624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1198292386673039 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43521197903 / 1000000000000) (-43521190490 / 1000000000000), orderedInterval (15271097181 / 1000000000000) (15271104594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (749835737080517 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14524489663 / 1000000000000) (-14524489516 / 1000000000000), orderedInterval (56475421677 / 1000000000000) (56475421824 / 1000000000000)))) (orderedInterval (3485027501 / 1000000000000) (3485033501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (403264153242939 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69676874995 / 1000000000000) (69676874996 / 1000000000000), orderedInterval (37861236116 / 1000000000000) (37861236117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1094940622105817 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44974601430 / 1000000000000) (-44974601429 / 1000000000000), orderedInterval (-17323600927 / 1000000000000) (-17323600925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1495047810132409 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26508046667 / 1000000000000) (-26508046666 / 1000000000000), orderedInterval (-31596797025 / 1000000000000) (-31596797024 / 1000000000000)))) (orderedInterval (-2916328939 / 1000000000000) (-2916328901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (632164262919483 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62495808888 / 1000000000000) (62495809431 / 1000000000000), orderedInterval (-11263295822 / 1000000000000) (-11263295280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2569712632057243 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22868064933 / 1000000000000) (22868072251 / 1000000000000), orderedInterval (-21651343250 / 1000000000000) (-21651335931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1716448947288437 / 4000000000000) 2 (IntervalRat.scale (691 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18494838696 / 1000000000000) (18494839450 / 1000000000000), orderedInterval (-33807871718 / 1000000000000) (-33807870964 / 1000000000000)))) (orderedInterval (11677892955 / 1000000000000) (11677895436 / 1000000000000))) = true
  rfl'

theorem compactCertificate474_chunkChecks2 :
    compactCertificate474.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate474.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate474_chunkChecks2_0
    compactCertificate474_chunkChecks2_1 compactCertificate474_chunkChecks2_2

theorem compactCertificate474_chunkChecks3_0 :
    compactCertificate474.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (691 / 2) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27975256112 / 1000000000000) (27975256113 / 1000000000000), orderedInterval (32516996345 / 1000000000000) (32516996346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1017974944999591 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36212815927 / 1000000000000) (-36212815926 / 1000000000000), orderedInterval (-34427349594 / 1000000000000) (-34427349593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (329192181597703 / 800000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26132825226 / 1000000000000) (-26132825225 / 1000000000000), orderedInterval (-29365243607 / 1000000000000) (-29365243606 / 1000000000000)))) (orderedInterval (-9823781826 / 1000000000000) (-9823781788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (297042550085237 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32084753149 / 1000000000000) (-32084752047 / 1000000000000), orderedInterval (87069294672 / 1000000000000) (87069295773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (797898072019889 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40629498509 / 1000000000000) (-40629443424 / 1000000000000), orderedInterval (39353943851 / 1000000000000) (39353998936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2166448478813613 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30527026694 / 1000000000000) (30527109025 / 1000000000000), orderedInterval (-15633162657 / 1000000000000) (-15633080326 / 1000000000000)))) (orderedInterval (-4565214026 / 1000000000000) (-4565190951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1595796144040469 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27283374603 / 1000000000000) (-27283374602 / 1000000000000), orderedInterval (-29143874024 / 1000000000000) (-29143874023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2734423892287337 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13983849765 / 1000000000000) (-13983849664 / 1000000000000), orderedInterval (27134372566 / 1000000000000) (27134372667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2014164262919483 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35377032523 / 1000000000000) (35377034309 / 1000000000000), orderedInterval (-3605927503 / 1000000000000) (-3605925716 / 1000000000000)))) (orderedInterval (6762717970 / 1000000000000) (6762718237 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate474_chunkChecks3_1 :
    compactCertificate474.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3090245944904309 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14136978058 / 1000000000000) (14136978059 / 1000000000000), orderedInterval (24974517591 / 1000000000000) (24974517592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1784154328152461 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24841223847 / 1000000000000) (24841223848 / 1000000000000), orderedInterval (28435969916 / 1000000000000) (28435969917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3166013164224049 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16181242207 / 1000000000000) (16181242208 / 1000000000000), orderedInterval (23281079851 / 1000000000000) (23281079852 / 1000000000000)))) (orderedInterval (5298129905 / 1000000000000) (5298131242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2958100182444181 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26222272748 / 1000000000000) (-26222201634 / 1000000000000), orderedInterval (13179897308 / 1000000000000) (13179968421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2111039870142373 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23865755918 / 1000000000000) (23865755919 / 1000000000000), orderedInterval (25210173190 / 1000000000000) (25210173191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2393694216059667 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24188322691 / 1000000000000) (24188334146 / 1000000000000), orderedInterval (-21900635910 / 1000000000000) (-21900624454 / 1000000000000)))) (orderedInterval (-6718959413 / 1000000000000) (-6718946317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1995612682183523 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6222467928 / 1000000000000) (-6222467927 / 1000000000000), orderedInterval (-35169326872 / 1000000000000) (-35169326871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1763184325569983 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37337713693 / 1000000000000) (37337716987 / 1000000000000), orderedInterval (-7123612305 / 1000000000000) (-7123609010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (511039540960317 / 800000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30420663521 / 1000000000000) (-30420642491 / 1000000000000), orderedInterval (8460119326 / 1000000000000) (8460140356 / 1000000000000)))) (orderedInterval (-1011055431 / 1000000000000) (-1011051519 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate474_chunkChecks3_2 :
    compactCertificate474.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1413562264833799 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31158384338 / 1000000000000) (31158417749 / 1000000000000), orderedInterval (-28864513035 / 1000000000000) (-28864479624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1198292386673039 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43521197903 / 1000000000000) (-43521190490 / 1000000000000), orderedInterval (15271097181 / 1000000000000) (15271104594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (749835737080517 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14524489663 / 1000000000000) (-14524489516 / 1000000000000), orderedInterval (56475421677 / 1000000000000) (56475421824 / 1000000000000)))) (orderedInterval (-4678971047 / 1000000000000) (-4678964965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (403264153242939 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69676874995 / 1000000000000) (69676874996 / 1000000000000), orderedInterval (37861236116 / 1000000000000) (37861236117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1094940622105817 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44974601430 / 1000000000000) (-44974601429 / 1000000000000), orderedInterval (-17323600927 / 1000000000000) (-17323600925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1495047810132409 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26508046667 / 1000000000000) (-26508046666 / 1000000000000), orderedInterval (-31596797025 / 1000000000000) (-31596797024 / 1000000000000)))) (orderedInterval (-3235353145 / 1000000000000) (-3235353106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (632164262919483 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62495808888 / 1000000000000) (62495809431 / 1000000000000), orderedInterval (-11263295822 / 1000000000000) (-11263295280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2569712632057243 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22868064933 / 1000000000000) (22868072251 / 1000000000000), orderedInterval (-21651343250 / 1000000000000) (-21651335931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1716448947288437 / 4000000000000) 3 (IntervalRat.scale (691 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18494838696 / 1000000000000) (18494839450 / 1000000000000), orderedInterval (-33807871718 / 1000000000000) (-33807870964 / 1000000000000)))) (orderedInterval (-23510606787 / 1000000000000) (-23510602372 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate474_chunkChecks3 :
    compactCertificate474.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate474.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate474_chunkChecks3_0
    compactCertificate474_chunkChecks3_1 compactCertificate474_chunkChecks3_2

theorem compactCertificate474_chunkChecks4_0 :
    compactCertificate474.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (691 / 2) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (27975256112 / 1000000000000) (27975256113 / 1000000000000), orderedInterval (32516996345 / 1000000000000) (32516996346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1017974944999591 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-36212815927 / 1000000000000) (-36212815926 / 1000000000000), orderedInterval (-34427349594 / 1000000000000) (-34427349593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (329192181597703 / 800000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26132825226 / 1000000000000) (-26132825225 / 1000000000000), orderedInterval (-29365243607 / 1000000000000) (-29365243606 / 1000000000000)))) (orderedInterval (7960332889 / 1000000000000) (7960332932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (297042550085237 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32084753149 / 1000000000000) (-32084752047 / 1000000000000), orderedInterval (87069294672 / 1000000000000) (87069295773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (797898072019889 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40629498509 / 1000000000000) (-40629443424 / 1000000000000), orderedInterval (39353943851 / 1000000000000) (39353998936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2166448478813613 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30527026694 / 1000000000000) (30527109025 / 1000000000000), orderedInterval (-15633162657 / 1000000000000) (-15633080326 / 1000000000000)))) (orderedInterval (-13243100969 / 1000000000000) (-13243065117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1595796144040469 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27283374603 / 1000000000000) (-27283374602 / 1000000000000), orderedInterval (-29143874024 / 1000000000000) (-29143874023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2734423892287337 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13983849765 / 1000000000000) (-13983849664 / 1000000000000), orderedInterval (27134372566 / 1000000000000) (27134372667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2014164262919483 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35377032523 / 1000000000000) (35377034309 / 1000000000000), orderedInterval (-3605927503 / 1000000000000) (-3605925716 / 1000000000000)))) (orderedInterval (10428772793 / 1000000000000) (10428773239 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate474_chunkChecks4_1 :
    compactCertificate474.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3090245944904309 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14136978058 / 1000000000000) (14136978059 / 1000000000000), orderedInterval (24974517591 / 1000000000000) (24974517592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1784154328152461 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24841223847 / 1000000000000) (24841223848 / 1000000000000), orderedInterval (28435969916 / 1000000000000) (28435969917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3166013164224049 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16181242207 / 1000000000000) (16181242208 / 1000000000000), orderedInterval (23281079851 / 1000000000000) (23281079852 / 1000000000000)))) (orderedInterval (5639752241 / 1000000000000) (5639755210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2958100182444181 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26222272748 / 1000000000000) (-26222201634 / 1000000000000), orderedInterval (13179897308 / 1000000000000) (13179968421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2111039870142373 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (23865755918 / 1000000000000) (23865755919 / 1000000000000), orderedInterval (25210173190 / 1000000000000) (25210173191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2393694216059667 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24188322691 / 1000000000000) (24188334146 / 1000000000000), orderedInterval (-21900635910 / 1000000000000) (-21900624454 / 1000000000000)))) (orderedInterval (21160921238 / 1000000000000) (21160949108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1995612682183523 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-6222467928 / 1000000000000) (-6222467927 / 1000000000000), orderedInterval (-35169326872 / 1000000000000) (-35169326871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1763184325569983 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37337713693 / 1000000000000) (37337716987 / 1000000000000), orderedInterval (-7123612305 / 1000000000000) (-7123609010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (511039540960317 / 800000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30420663521 / 1000000000000) (-30420642491 / 1000000000000), orderedInterval (8460119326 / 1000000000000) (8460140356 / 1000000000000)))) (orderedInterval (-15069760615 / 1000000000000) (-15069753628 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate474_chunkChecks4_2 :
    compactCertificate474.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1413562264833799 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31158384338 / 1000000000000) (31158417749 / 1000000000000), orderedInterval (-28864513035 / 1000000000000) (-28864479624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1198292386673039 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43521197903 / 1000000000000) (-43521190490 / 1000000000000), orderedInterval (15271097181 / 1000000000000) (15271104594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (749835737080517 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14524489663 / 1000000000000) (-14524489516 / 1000000000000), orderedInterval (56475421677 / 1000000000000) (56475421824 / 1000000000000)))) (orderedInterval (-4074496981 / 1000000000000) (-4074490788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (403264153242939 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69676874995 / 1000000000000) (69676874996 / 1000000000000), orderedInterval (37861236116 / 1000000000000) (37861236117 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1094940622105817 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44974601430 / 1000000000000) (-44974601429 / 1000000000000), orderedInterval (-17323600927 / 1000000000000) (-17323600925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1495047810132409 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26508046667 / 1000000000000) (-26508046666 / 1000000000000), orderedInterval (-31596797025 / 1000000000000) (-31596797024 / 1000000000000)))) (orderedInterval (3193789444 / 1000000000000) (3193789484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (632164262919483 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62495808888 / 1000000000000) (62495809431 / 1000000000000), orderedInterval (-11263295822 / 1000000000000) (-11263295280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2569712632057243 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22868064933 / 1000000000000) (22868072251 / 1000000000000), orderedInterval (-21651343250 / 1000000000000) (-21651335931 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1716448947288437 / 4000000000000) 4 (IntervalRat.scale (691 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18494838696 / 1000000000000) (18494839450 / 1000000000000), orderedInterval (-33807871718 / 1000000000000) (-33807870964 / 1000000000000)))) (orderedInterval (-30356600054 / 1000000000000) (-30356592081 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate474_chunkChecks4 :
    compactCertificate474.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate474.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate474_chunkChecks4_0
    compactCertificate474_chunkChecks4_1 compactCertificate474_chunkChecks4_2

theorem compactCertificate474_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate474.chunkCheck r b = true :=
  compactCertificate474.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate474_chunkChecks0
    · exact compactCertificate474_chunkChecks1
    · exact compactCertificate474_chunkChecks2
    · exact compactCertificate474_chunkChecks3
    · exact compactCertificate474_chunkChecks4)

theorem compactCertificate474_coefficient0 :
    compactCertificate474.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate474_coefficient1 :
    compactCertificate474.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate474_coefficient2 :
    compactCertificate474.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate474_coefficient3 :
    compactCertificate474.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate474_coefficient4 :
    compactCertificate474.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate474_coefficients : ∀ r : Fin 5,
    compactCertificate474.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate474_coefficient0
  · exact compactCertificate474_coefficient1
  · exact compactCertificate474_coefficient2
  · exact compactCertificate474_coefficient3
  · exact compactCertificate474_coefficient4

theorem compactCertificate474_lower : (1 : ℚ) ≤ compactCertificate474.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate474, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate474_proves {t : ℝ} (ht : t ∈ compactCertificate474.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate474.proves compactCertificate474_states compactCertificate474_chunks
    compactCertificate474_coefficients compactCertificate474_lower ht

end Erdos232
