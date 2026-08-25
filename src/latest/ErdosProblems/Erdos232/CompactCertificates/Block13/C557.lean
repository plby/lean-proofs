/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate557 : CompactCertificate where
  left := 428
  right := 429
  center := 857 / 2
  grid := fun i =>
    match i.val with
    | 0 => 136
    | 1 => 101
    | 2 => 163
    | 3 => 29
    | 4 => 79
    | 5 => 214
    | 6 => 158
    | 7 => 270
    | 8 => 199
    | 9 => 305
    | 10 => 176
    | 11 => 313
    | 12 => 292
    | 13 => 208
    | 14 => 236
    | 15 => 197
    | 16 => 174
    | 17 => 252
    | 18 => 140
    | 19 => 118
    | 20 => 74
    | 21 => 40
    | 22 => 108
    | 23 => 148
    | 24 => 62
    | 25 => 254
    | _ => 169
  point := fun i =>
    match i.val with
    | 0 => 857 / 2
    | 1 => 1262524642351157 / 4000000000000
    | 2 => 408274529130581 / 800000000000
    | 3 => 368401541856799 / 4000000000000
    | 4 => 989578361390803 / 4000000000000
    | 5 => 2686897751582151 / 4000000000000
    | 6 => 1979156722782463 / 4000000000000
    | 7 => 3391318778133499 / 4000000000000
    | 8 => 2498030062694641 / 4000000000000
    | 9 => 3832620513434143 / 4000000000000
    | 10 => 2212764485132647 / 4000000000000
    | 11 => 3926589409175123 / 4000000000000
    | 12 => 3668729169833087 / 4000000000000
    | 13 => 2618178247050671 / 4000000000000
    | 14 => 2968735084172409 / 4000000000000
    | 15 => 2475021806991721 / 4000000000000
    | 16 => 2186756826358141 / 4000000000000
    | 17 => 633807361219959 / 800000000000
    | 18 => 1753144516588373 / 4000000000000
    | 19 => 1486160022255853 / 4000000000000
    | 20 => 929969937305359 / 4000000000000
    | 21 => 500140925223153 / 4000000000000
    | 22 => 1357979903248459 / 4000000000000
    | 23 => 1854205460612843 / 4000000000000
    | 24 => 784030062694641 / 4000000000000
    | 25 => 3187038676806161 / 4000000000000
    | _ => 2128794135783199 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (34577147156 / 1000000000000) (34577191146 / 1000000000000), orderedInterval (-17073056234 / 1000000000000) (-17073012245 / 1000000000000))
    | 1 => (orderedInterval (34748363097 / 1000000000000) (34748430568 / 1000000000000), orderedInterval (-28507180574 / 1000000000000) (-28507113103 / 1000000000000))
    | 2 => (orderedInterval (28755458136 / 1000000000000) (28755509197 / 1000000000000), orderedInterval (-20535675116 / 1000000000000) (-20535624055 / 1000000000000))
    | 3 => (orderedInterval (-81356810016 / 1000000000000) (-81356809477 / 1000000000000), orderedInterval (17565159135 / 1000000000000) (17565159673 / 1000000000000))
    | 4 => (orderedInterval (321427545 / 1000000000000) (321427548 / 1000000000000), orderedInterval (-50727358573 / 1000000000000) (-50727358571 / 1000000000000))
    | 5 => (orderedInterval (6382046068 / 1000000000000) (6382046069 / 1000000000000), orderedInterval (30111843144 / 1000000000000) (30111843145 / 1000000000000))
    | 6 => (orderedInterval (-25664237082 / 1000000000000) (-25664223890 / 1000000000000), orderedInterval (25085771715 / 1000000000000) (25085784907 / 1000000000000))
    | 7 => (orderedInterval (10289344779 / 1000000000000) (10289344780 / 1000000000000), orderedInterval (25391001516 / 1000000000000) (25391001517 / 1000000000000))
    | 8 => (orderedInterval (-3688226701 / 1000000000000) (-3688226700 / 1000000000000), orderedInterval (-31711274110 / 1000000000000) (-31711274109 / 1000000000000))
    | 9 => (orderedInterval (-17657448178 / 1000000000000) (-17657448177 / 1000000000000), orderedInterval (-18769416481 / 1000000000000) (-18769416480 / 1000000000000))
    | 10 => (orderedInterval (29526668217 / 1000000000000) (29526668218 / 1000000000000), orderedInterval (16676277832 / 1000000000000) (16676277834 / 1000000000000))
    | 11 => (orderedInterval (19722731502 / 1000000000000) (19722734049 / 1000000000000), orderedInterval (-16120157472 / 1000000000000) (-16120154925 / 1000000000000))
    | 12 => (orderedInterval (15361411522 / 1000000000000) (15361411523 / 1000000000000), orderedInterval (21395619130 / 1000000000000) (21395619131 / 1000000000000))
    | 13 => (orderedInterval (29721987733 / 1000000000000) (29722019694 / 1000000000000), orderedInterval (-9468200777 / 1000000000000) (-9468168816 / 1000000000000))
    | 14 => (orderedInterval (29283064981 / 1000000000000) (29283066823 / 1000000000000), orderedInterval (497516702 / 1000000000000) (497518545 / 1000000000000))
    | 15 => (orderedInterval (-19332594303 / 1000000000000) (-19332594302 / 1000000000000), orderedInterval (-25579734153 / 1000000000000) (-25579734152 / 1000000000000))
    | 16 => (orderedInterval (25348141758 / 1000000000000) (25348141759 / 1000000000000), orderedInterval (22823523439 / 1000000000000) (22823523440 / 1000000000000))
    | 17 => (orderedInterval (27737695110 / 1000000000000) (27737695356 / 1000000000000), orderedInterval (5828003743 / 1000000000000) (5828003989 / 1000000000000))
    | 18 => (orderedInterval (-26026768102 / 1000000000000) (-26026756934 / 1000000000000), orderedInterval (27870817395 / 1000000000000) (27870828563 / 1000000000000))
    | 19 => (orderedInterval (41349536563 / 1000000000000) (41349536980 / 1000000000000), orderedInterval (-1973068786 / 1000000000000) (-1973068369 / 1000000000000))
    | 20 => (orderedInterval (37519239190 / 1000000000000) (37519239191 / 1000000000000), orderedInterval (36395941906 / 1000000000000) (36395941907 / 1000000000000))
    | 21 => (orderedInterval (11080845214 / 1000000000000) (11080845215 / 1000000000000), orderedInterval (70445240404 / 1000000000000) (70445240405 / 1000000000000))
    | 22 => (orderedInterval (36155251576 / 1000000000000) (36155251577 / 1000000000000), orderedInterval (23779364245 / 1000000000000) (23779364246 / 1000000000000))
    | 23 => (orderedInterval (-21508889249 / 1000000000000) (-21508886812 / 1000000000000), orderedInterval (30201357197 / 1000000000000) (30201359633 / 1000000000000))
    | 24 => (orderedInterval (51495715341 / 1000000000000) (51495728114 / 1000000000000), orderedInterval (-24546924410 / 1000000000000) (-24546911637 / 1000000000000))
    | 25 => (orderedInterval (-11516357774 / 1000000000000) (-11516357756 / 1000000000000), orderedInterval (25821654141 / 1000000000000) (25821654160 / 1000000000000))
    | _ => (orderedInterval (-30617859725 / 1000000000000) (-30617772800 / 1000000000000), orderedInterval (16114623429 / 1000000000000) (16114710354 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15716361072 / 1000000000000) (15716382164 / 1000000000000)
      | 1 => orderedInterval (440702192 / 1000000000000) (440702250 / 1000000000000)
      | 2 => orderedInterval (-406501735 / 1000000000000) (-406501711 / 1000000000000)
      | 3 => orderedInterval (8128900889 / 1000000000000) (8128901422 / 1000000000000)
      | 4 => orderedInterval (2385086249 / 1000000000000) (2385089332 / 1000000000000)
      | 5 => orderedInterval (-963641802 / 1000000000000) (-963641754 / 1000000000000)
      | 6 => orderedInterval (3042548696 / 1000000000000) (3042550613 / 1000000000000)
      | 7 => orderedInterval (623558448 / 1000000000000) (623558686 / 1000000000000)
      | _ => orderedInterval (6992591364 / 1000000000000) (6992607871 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8398046608 / 1000000000000) (-8398025107 / 1000000000000)
      | 1 => orderedInterval (-4466003111 / 1000000000000) (-4466003051 / 1000000000000)
      | 2 => orderedInterval (-2666530381 / 1000000000000) (-2666530339 / 1000000000000)
      | 3 => orderedInterval (3802875244 / 1000000000000) (3802876426 / 1000000000000)
      | 4 => orderedInterval (-2198778840 / 1000000000000) (-2198774124 / 1000000000000)
      | 5 => orderedInterval (-1817012157 / 1000000000000) (-1817012086 / 1000000000000)
      | 6 => orderedInterval (-3818394830 / 1000000000000) (-3818392883 / 1000000000000)
      | 7 => orderedInterval (-3310919134 / 1000000000000) (-3310918886 / 1000000000000)
      | _ => orderedInterval (-7731304223 / 1000000000000) (-7731283762 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16254818319 / 1000000000000) (-16254796202 / 1000000000000)
      | 1 => orderedInterval (1080661494 / 1000000000000) (1080661576 / 1000000000000)
      | 2 => orderedInterval (1437994584 / 1000000000000) (1437994659 / 1000000000000)
      | 3 => orderedInterval (-34056948922 / 1000000000000) (-34056946265 / 1000000000000)
      | 4 => orderedInterval (-4837814981 / 1000000000000) (-4837807753 / 1000000000000)
      | 5 => orderedInterval (403108704 / 1000000000000) (403108814 / 1000000000000)
      | 6 => orderedInterval (-2944872241 / 1000000000000) (-2944870256 / 1000000000000)
      | 7 => orderedInterval (-1389094390 / 1000000000000) (-1389094124 / 1000000000000)
      | _ => orderedInterval (-12149737747 / 1000000000000) (-12149712273 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8947021003 / 1000000000000) (8947043848 / 1000000000000)
      | 1 => orderedInterval (8602195673 / 1000000000000) (8602195795 / 1000000000000)
      | 2 => orderedInterval (8435480432 / 1000000000000) (8435480567 / 1000000000000)
      | 3 => orderedInterval (-12314890902 / 1000000000000) (-12314884890 / 1000000000000)
      | 4 => orderedInterval (7003377038 / 1000000000000) (7003388108 / 1000000000000)
      | 5 => orderedInterval (2657683063 / 1000000000000) (2657683239 / 1000000000000)
      | 6 => orderedInterval (4513479392 / 1000000000000) (4513481415 / 1000000000000)
      | 7 => orderedInterval (3234173886 / 1000000000000) (3234174170 / 1000000000000)
      | _ => orderedInterval (19348067085 / 1000000000000) (19348098788 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (17153835691 / 1000000000000) (17153859499 / 1000000000000)
      | 1 => orderedInterval (-2776811407 / 1000000000000) (-2776811220 / 1000000000000)
      | 2 => orderedInterval (-5305486928 / 1000000000000) (-5305486677 / 1000000000000)
      | 3 => orderedInterval (161795775464 / 1000000000000) (161795789132 / 1000000000000)
      | 4 => orderedInterval (8114660680 / 1000000000000) (8114677673 / 1000000000000)
      | 5 => orderedInterval (3473000921 / 1000000000000) (3473001210 / 1000000000000)
      | 6 => orderedInterval (3316802219 / 1000000000000) (3316804287 / 1000000000000)
      | 7 => orderedInterval (1917852887 / 1000000000000) (1917853194 / 1000000000000)
      | _ => orderedInterval (24799041832 / 1000000000000) (24799081416 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (35959605373 / 1000000000000) (35959648873 / 1000000000000)
    | 1 => orderedInterval (-30604114040 / 1000000000000) (-30604063812 / 1000000000000)
    | 2 => orderedInterval (-68711521818 / 1000000000000) (-68711461824 / 1000000000000)
    | 3 => orderedInterval (50426586670 / 1000000000000) (50426661040 / 1000000000000)
    | _ => orderedInterval (212488671359 / 1000000000000) (212488768514 / 1000000000000)

theorem compactCertificate557_stateChecks0 :
    compactCertificate557.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (857 / 2)) (orderedInterval (34577147156 / 1000000000000) (34577191146 / 1000000000000), orderedInterval (-17073056234 / 1000000000000) (-17073012245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1262524642351157 / 4000000000000)) (orderedInterval (34748363097 / 1000000000000) (34748430568 / 1000000000000), orderedInterval (-28507180574 / 1000000000000) (-28507113103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (408274529130581 / 800000000000)) (orderedInterval (28755458136 / 1000000000000) (28755509197 / 1000000000000), orderedInterval (-20535675116 / 1000000000000) (-20535624055 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks1 :
    compactCertificate557.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (368401541856799 / 4000000000000)) (orderedInterval (-81356810016 / 1000000000000) (-81356809477 / 1000000000000), orderedInterval (17565159135 / 1000000000000) (17565159673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (989578361390803 / 4000000000000)) (orderedInterval (321427545 / 1000000000000) (321427548 / 1000000000000), orderedInterval (-50727358573 / 1000000000000) (-50727358571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2686897751582151 / 4000000000000)) (orderedInterval (6382046068 / 1000000000000) (6382046069 / 1000000000000), orderedInterval (30111843144 / 1000000000000) (30111843145 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks2 :
    compactCertificate557.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1979156722782463 / 4000000000000)) (orderedInterval (-25664237082 / 1000000000000) (-25664223890 / 1000000000000), orderedInterval (25085771715 / 1000000000000) (25085784907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3391318778133499 / 4000000000000)) (orderedInterval (10289344779 / 1000000000000) (10289344780 / 1000000000000), orderedInterval (25391001516 / 1000000000000) (25391001517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2498030062694641 / 4000000000000)) (orderedInterval (-3688226701 / 1000000000000) (-3688226700 / 1000000000000), orderedInterval (-31711274110 / 1000000000000) (-31711274109 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks3 :
    compactCertificate557.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 305 12 (3832620513434143 / 4000000000000)) (orderedInterval (-17657448178 / 1000000000000) (-17657448177 / 1000000000000), orderedInterval (-18769416481 / 1000000000000) (-18769416480 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2212764485132647 / 4000000000000)) (orderedInterval (29526668217 / 1000000000000) (29526668218 / 1000000000000), orderedInterval (16676277832 / 1000000000000) (16676277834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 313 12 (3926589409175123 / 4000000000000)) (orderedInterval (19722731502 / 1000000000000) (19722734049 / 1000000000000), orderedInterval (-16120157472 / 1000000000000) (-16120154925 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks4 :
    compactCertificate557.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (3668729169833087 / 4000000000000)) (orderedInterval (15361411522 / 1000000000000) (15361411523 / 1000000000000), orderedInterval (21395619130 / 1000000000000) (21395619131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2618178247050671 / 4000000000000)) (orderedInterval (29721987733 / 1000000000000) (29722019694 / 1000000000000), orderedInterval (-9468200777 / 1000000000000) (-9468168816 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2968735084172409 / 4000000000000)) (orderedInterval (29283064981 / 1000000000000) (29283066823 / 1000000000000), orderedInterval (497516702 / 1000000000000) (497518545 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks5 :
    compactCertificate557.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2475021806991721 / 4000000000000)) (orderedInterval (-19332594303 / 1000000000000) (-19332594302 / 1000000000000), orderedInterval (-25579734153 / 1000000000000) (-25579734152 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2186756826358141 / 4000000000000)) (orderedInterval (25348141758 / 1000000000000) (25348141759 / 1000000000000), orderedInterval (22823523439 / 1000000000000) (22823523440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (633807361219959 / 800000000000)) (orderedInterval (27737695110 / 1000000000000) (27737695356 / 1000000000000), orderedInterval (5828003743 / 1000000000000) (5828003989 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks6 :
    compactCertificate557.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1753144516588373 / 4000000000000)) (orderedInterval (-26026768102 / 1000000000000) (-26026756934 / 1000000000000), orderedInterval (27870817395 / 1000000000000) (27870828563 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1486160022255853 / 4000000000000)) (orderedInterval (41349536563 / 1000000000000) (41349536980 / 1000000000000), orderedInterval (-1973068786 / 1000000000000) (-1973068369 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (929969937305359 / 4000000000000)) (orderedInterval (37519239190 / 1000000000000) (37519239191 / 1000000000000), orderedInterval (36395941906 / 1000000000000) (36395941907 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks7 :
    compactCertificate557.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (500140925223153 / 4000000000000)) (orderedInterval (11080845214 / 1000000000000) (11080845215 / 1000000000000), orderedInterval (70445240404 / 1000000000000) (70445240405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1357979903248459 / 4000000000000)) (orderedInterval (36155251576 / 1000000000000) (36155251577 / 1000000000000), orderedInterval (23779364245 / 1000000000000) (23779364246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1854205460612843 / 4000000000000)) (orderedInterval (-21508889249 / 1000000000000) (-21508886812 / 1000000000000), orderedInterval (30201357197 / 1000000000000) (30201359633 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_stateChecks8 :
    compactCertificate557.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (784030062694641 / 4000000000000)) (orderedInterval (51495715341 / 1000000000000) (51495728114 / 1000000000000), orderedInterval (-24546924410 / 1000000000000) (-24546911637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (3187038676806161 / 4000000000000)) (orderedInterval (-11516357774 / 1000000000000) (-11516357756 / 1000000000000), orderedInterval (25821654141 / 1000000000000) (25821654160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2128794135783199 / 4000000000000)) (orderedInterval (-30617859725 / 1000000000000) (-30617772800 / 1000000000000), orderedInterval (16114623429 / 1000000000000) (16114710354 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_states : ∀ j,
    BesselStateValid (compactCertificate557.point j) (compactCertificate557.state j) :=
  compactCertificate557.statesValid_of_checks3 compactCertificate557_stateChecks0
    compactCertificate557_stateChecks1 compactCertificate557_stateChecks2
    compactCertificate557_stateChecks3 compactCertificate557_stateChecks4
    compactCertificate557_stateChecks5 compactCertificate557_stateChecks6
    compactCertificate557_stateChecks7 compactCertificate557_stateChecks8

theorem compactCertificate557_chunkChecks0_0 :
    compactCertificate557.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (857 / 2) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34577147156 / 1000000000000) (34577191146 / 1000000000000), orderedInterval (-17073056234 / 1000000000000) (-17073012245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1262524642351157 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34748363097 / 1000000000000) (34748430568 / 1000000000000), orderedInterval (-28507180574 / 1000000000000) (-28507113103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (408274529130581 / 800000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28755458136 / 1000000000000) (28755509197 / 1000000000000), orderedInterval (-20535675116 / 1000000000000) (-20535624055 / 1000000000000)))) (orderedInterval (15716361072 / 1000000000000) (15716382164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (368401541856799 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81356810016 / 1000000000000) (-81356809477 / 1000000000000), orderedInterval (17565159135 / 1000000000000) (17565159673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (989578361390803 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (321427545 / 1000000000000) (321427548 / 1000000000000), orderedInterval (-50727358573 / 1000000000000) (-50727358571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2686897751582151 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6382046068 / 1000000000000) (6382046069 / 1000000000000), orderedInterval (30111843144 / 1000000000000) (30111843145 / 1000000000000)))) (orderedInterval (440702192 / 1000000000000) (440702250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1979156722782463 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664237082 / 1000000000000) (-25664223890 / 1000000000000), orderedInterval (25085771715 / 1000000000000) (25085784907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3391318778133499 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10289344779 / 1000000000000) (10289344780 / 1000000000000), orderedInterval (25391001516 / 1000000000000) (25391001517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2498030062694641 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3688226701 / 1000000000000) (-3688226700 / 1000000000000), orderedInterval (-31711274110 / 1000000000000) (-31711274109 / 1000000000000)))) (orderedInterval (-406501735 / 1000000000000) (-406501711 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks0_1 :
    compactCertificate557.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3832620513434143 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17657448178 / 1000000000000) (-17657448177 / 1000000000000), orderedInterval (-18769416481 / 1000000000000) (-18769416480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2212764485132647 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29526668217 / 1000000000000) (29526668218 / 1000000000000), orderedInterval (16676277832 / 1000000000000) (16676277834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3926589409175123 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19722731502 / 1000000000000) (19722734049 / 1000000000000), orderedInterval (-16120157472 / 1000000000000) (-16120154925 / 1000000000000)))) (orderedInterval (8128900889 / 1000000000000) (8128901422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3668729169833087 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15361411522 / 1000000000000) (15361411523 / 1000000000000), orderedInterval (21395619130 / 1000000000000) (21395619131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2618178247050671 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29721987733 / 1000000000000) (29722019694 / 1000000000000), orderedInterval (-9468200777 / 1000000000000) (-9468168816 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2968735084172409 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29283064981 / 1000000000000) (29283066823 / 1000000000000), orderedInterval (497516702 / 1000000000000) (497518545 / 1000000000000)))) (orderedInterval (2385086249 / 1000000000000) (2385089332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2475021806991721 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19332594303 / 1000000000000) (-19332594302 / 1000000000000), orderedInterval (-25579734153 / 1000000000000) (-25579734152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2186756826358141 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25348141758 / 1000000000000) (25348141759 / 1000000000000), orderedInterval (22823523439 / 1000000000000) (22823523440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (633807361219959 / 800000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27737695110 / 1000000000000) (27737695356 / 1000000000000), orderedInterval (5828003743 / 1000000000000) (5828003989 / 1000000000000)))) (orderedInterval (-963641802 / 1000000000000) (-963641754 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks0_2 :
    compactCertificate557.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1753144516588373 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26026768102 / 1000000000000) (-26026756934 / 1000000000000), orderedInterval (27870817395 / 1000000000000) (27870828563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1486160022255853 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41349536563 / 1000000000000) (41349536980 / 1000000000000), orderedInterval (-1973068786 / 1000000000000) (-1973068369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (929969937305359 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (37519239190 / 1000000000000) (37519239191 / 1000000000000), orderedInterval (36395941906 / 1000000000000) (36395941907 / 1000000000000)))) (orderedInterval (3042548696 / 1000000000000) (3042550613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (500140925223153 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11080845214 / 1000000000000) (11080845215 / 1000000000000), orderedInterval (70445240404 / 1000000000000) (70445240405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1357979903248459 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36155251576 / 1000000000000) (36155251577 / 1000000000000), orderedInterval (23779364245 / 1000000000000) (23779364246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1854205460612843 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21508889249 / 1000000000000) (-21508886812 / 1000000000000), orderedInterval (30201357197 / 1000000000000) (30201359633 / 1000000000000)))) (orderedInterval (623558448 / 1000000000000) (623558686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (784030062694641 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51495715341 / 1000000000000) (51495728114 / 1000000000000), orderedInterval (-24546924410 / 1000000000000) (-24546911637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3187038676806161 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11516357774 / 1000000000000) (-11516357756 / 1000000000000), orderedInterval (25821654141 / 1000000000000) (25821654160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2128794135783199 / 4000000000000) 0 (IntervalRat.scale (857 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30617859725 / 1000000000000) (-30617772800 / 1000000000000), orderedInterval (16114623429 / 1000000000000) (16114710354 / 1000000000000)))) (orderedInterval (6992591364 / 1000000000000) (6992607871 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks0 :
    compactCertificate557.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate557.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate557_chunkChecks0_0
    compactCertificate557_chunkChecks0_1 compactCertificate557_chunkChecks0_2

theorem compactCertificate557_chunkChecks1_0 :
    compactCertificate557.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (857 / 2) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34577147156 / 1000000000000) (34577191146 / 1000000000000), orderedInterval (-17073056234 / 1000000000000) (-17073012245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1262524642351157 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34748363097 / 1000000000000) (34748430568 / 1000000000000), orderedInterval (-28507180574 / 1000000000000) (-28507113103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (408274529130581 / 800000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28755458136 / 1000000000000) (28755509197 / 1000000000000), orderedInterval (-20535675116 / 1000000000000) (-20535624055 / 1000000000000)))) (orderedInterval (-8398046608 / 1000000000000) (-8398025107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (368401541856799 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81356810016 / 1000000000000) (-81356809477 / 1000000000000), orderedInterval (17565159135 / 1000000000000) (17565159673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (989578361390803 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (321427545 / 1000000000000) (321427548 / 1000000000000), orderedInterval (-50727358573 / 1000000000000) (-50727358571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2686897751582151 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6382046068 / 1000000000000) (6382046069 / 1000000000000), orderedInterval (30111843144 / 1000000000000) (30111843145 / 1000000000000)))) (orderedInterval (-4466003111 / 1000000000000) (-4466003051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1979156722782463 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664237082 / 1000000000000) (-25664223890 / 1000000000000), orderedInterval (25085771715 / 1000000000000) (25085784907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3391318778133499 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10289344779 / 1000000000000) (10289344780 / 1000000000000), orderedInterval (25391001516 / 1000000000000) (25391001517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2498030062694641 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3688226701 / 1000000000000) (-3688226700 / 1000000000000), orderedInterval (-31711274110 / 1000000000000) (-31711274109 / 1000000000000)))) (orderedInterval (-2666530381 / 1000000000000) (-2666530339 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks1_1 :
    compactCertificate557.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3832620513434143 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17657448178 / 1000000000000) (-17657448177 / 1000000000000), orderedInterval (-18769416481 / 1000000000000) (-18769416480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2212764485132647 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29526668217 / 1000000000000) (29526668218 / 1000000000000), orderedInterval (16676277832 / 1000000000000) (16676277834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3926589409175123 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19722731502 / 1000000000000) (19722734049 / 1000000000000), orderedInterval (-16120157472 / 1000000000000) (-16120154925 / 1000000000000)))) (orderedInterval (3802875244 / 1000000000000) (3802876426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3668729169833087 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15361411522 / 1000000000000) (15361411523 / 1000000000000), orderedInterval (21395619130 / 1000000000000) (21395619131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2618178247050671 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29721987733 / 1000000000000) (29722019694 / 1000000000000), orderedInterval (-9468200777 / 1000000000000) (-9468168816 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2968735084172409 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29283064981 / 1000000000000) (29283066823 / 1000000000000), orderedInterval (497516702 / 1000000000000) (497518545 / 1000000000000)))) (orderedInterval (-2198778840 / 1000000000000) (-2198774124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2475021806991721 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19332594303 / 1000000000000) (-19332594302 / 1000000000000), orderedInterval (-25579734153 / 1000000000000) (-25579734152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2186756826358141 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25348141758 / 1000000000000) (25348141759 / 1000000000000), orderedInterval (22823523439 / 1000000000000) (22823523440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (633807361219959 / 800000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27737695110 / 1000000000000) (27737695356 / 1000000000000), orderedInterval (5828003743 / 1000000000000) (5828003989 / 1000000000000)))) (orderedInterval (-1817012157 / 1000000000000) (-1817012086 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks1_2 :
    compactCertificate557.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1753144516588373 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26026768102 / 1000000000000) (-26026756934 / 1000000000000), orderedInterval (27870817395 / 1000000000000) (27870828563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1486160022255853 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41349536563 / 1000000000000) (41349536980 / 1000000000000), orderedInterval (-1973068786 / 1000000000000) (-1973068369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (929969937305359 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (37519239190 / 1000000000000) (37519239191 / 1000000000000), orderedInterval (36395941906 / 1000000000000) (36395941907 / 1000000000000)))) (orderedInterval (-3818394830 / 1000000000000) (-3818392883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (500140925223153 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11080845214 / 1000000000000) (11080845215 / 1000000000000), orderedInterval (70445240404 / 1000000000000) (70445240405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1357979903248459 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36155251576 / 1000000000000) (36155251577 / 1000000000000), orderedInterval (23779364245 / 1000000000000) (23779364246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1854205460612843 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21508889249 / 1000000000000) (-21508886812 / 1000000000000), orderedInterval (30201357197 / 1000000000000) (30201359633 / 1000000000000)))) (orderedInterval (-3310919134 / 1000000000000) (-3310918886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (784030062694641 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51495715341 / 1000000000000) (51495728114 / 1000000000000), orderedInterval (-24546924410 / 1000000000000) (-24546911637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3187038676806161 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11516357774 / 1000000000000) (-11516357756 / 1000000000000), orderedInterval (25821654141 / 1000000000000) (25821654160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2128794135783199 / 4000000000000) 1 (IntervalRat.scale (857 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30617859725 / 1000000000000) (-30617772800 / 1000000000000), orderedInterval (16114623429 / 1000000000000) (16114710354 / 1000000000000)))) (orderedInterval (-7731304223 / 1000000000000) (-7731283762 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks1 :
    compactCertificate557.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate557.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate557_chunkChecks1_0
    compactCertificate557_chunkChecks1_1 compactCertificate557_chunkChecks1_2

theorem compactCertificate557_chunkChecks2_0 :
    compactCertificate557.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (857 / 2) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34577147156 / 1000000000000) (34577191146 / 1000000000000), orderedInterval (-17073056234 / 1000000000000) (-17073012245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1262524642351157 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34748363097 / 1000000000000) (34748430568 / 1000000000000), orderedInterval (-28507180574 / 1000000000000) (-28507113103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (408274529130581 / 800000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28755458136 / 1000000000000) (28755509197 / 1000000000000), orderedInterval (-20535675116 / 1000000000000) (-20535624055 / 1000000000000)))) (orderedInterval (-16254818319 / 1000000000000) (-16254796202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (368401541856799 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81356810016 / 1000000000000) (-81356809477 / 1000000000000), orderedInterval (17565159135 / 1000000000000) (17565159673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (989578361390803 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (321427545 / 1000000000000) (321427548 / 1000000000000), orderedInterval (-50727358573 / 1000000000000) (-50727358571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2686897751582151 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6382046068 / 1000000000000) (6382046069 / 1000000000000), orderedInterval (30111843144 / 1000000000000) (30111843145 / 1000000000000)))) (orderedInterval (1080661494 / 1000000000000) (1080661576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1979156722782463 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664237082 / 1000000000000) (-25664223890 / 1000000000000), orderedInterval (25085771715 / 1000000000000) (25085784907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3391318778133499 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10289344779 / 1000000000000) (10289344780 / 1000000000000), orderedInterval (25391001516 / 1000000000000) (25391001517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2498030062694641 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3688226701 / 1000000000000) (-3688226700 / 1000000000000), orderedInterval (-31711274110 / 1000000000000) (-31711274109 / 1000000000000)))) (orderedInterval (1437994584 / 1000000000000) (1437994659 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks2_1 :
    compactCertificate557.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3832620513434143 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17657448178 / 1000000000000) (-17657448177 / 1000000000000), orderedInterval (-18769416481 / 1000000000000) (-18769416480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2212764485132647 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29526668217 / 1000000000000) (29526668218 / 1000000000000), orderedInterval (16676277832 / 1000000000000) (16676277834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3926589409175123 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19722731502 / 1000000000000) (19722734049 / 1000000000000), orderedInterval (-16120157472 / 1000000000000) (-16120154925 / 1000000000000)))) (orderedInterval (-34056948922 / 1000000000000) (-34056946265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3668729169833087 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15361411522 / 1000000000000) (15361411523 / 1000000000000), orderedInterval (21395619130 / 1000000000000) (21395619131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2618178247050671 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29721987733 / 1000000000000) (29722019694 / 1000000000000), orderedInterval (-9468200777 / 1000000000000) (-9468168816 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2968735084172409 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29283064981 / 1000000000000) (29283066823 / 1000000000000), orderedInterval (497516702 / 1000000000000) (497518545 / 1000000000000)))) (orderedInterval (-4837814981 / 1000000000000) (-4837807753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2475021806991721 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19332594303 / 1000000000000) (-19332594302 / 1000000000000), orderedInterval (-25579734153 / 1000000000000) (-25579734152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2186756826358141 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25348141758 / 1000000000000) (25348141759 / 1000000000000), orderedInterval (22823523439 / 1000000000000) (22823523440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (633807361219959 / 800000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27737695110 / 1000000000000) (27737695356 / 1000000000000), orderedInterval (5828003743 / 1000000000000) (5828003989 / 1000000000000)))) (orderedInterval (403108704 / 1000000000000) (403108814 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks2_2 :
    compactCertificate557.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1753144516588373 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26026768102 / 1000000000000) (-26026756934 / 1000000000000), orderedInterval (27870817395 / 1000000000000) (27870828563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1486160022255853 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41349536563 / 1000000000000) (41349536980 / 1000000000000), orderedInterval (-1973068786 / 1000000000000) (-1973068369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (929969937305359 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (37519239190 / 1000000000000) (37519239191 / 1000000000000), orderedInterval (36395941906 / 1000000000000) (36395941907 / 1000000000000)))) (orderedInterval (-2944872241 / 1000000000000) (-2944870256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (500140925223153 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11080845214 / 1000000000000) (11080845215 / 1000000000000), orderedInterval (70445240404 / 1000000000000) (70445240405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1357979903248459 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36155251576 / 1000000000000) (36155251577 / 1000000000000), orderedInterval (23779364245 / 1000000000000) (23779364246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1854205460612843 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21508889249 / 1000000000000) (-21508886812 / 1000000000000), orderedInterval (30201357197 / 1000000000000) (30201359633 / 1000000000000)))) (orderedInterval (-1389094390 / 1000000000000) (-1389094124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (784030062694641 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51495715341 / 1000000000000) (51495728114 / 1000000000000), orderedInterval (-24546924410 / 1000000000000) (-24546911637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3187038676806161 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11516357774 / 1000000000000) (-11516357756 / 1000000000000), orderedInterval (25821654141 / 1000000000000) (25821654160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2128794135783199 / 4000000000000) 2 (IntervalRat.scale (857 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30617859725 / 1000000000000) (-30617772800 / 1000000000000), orderedInterval (16114623429 / 1000000000000) (16114710354 / 1000000000000)))) (orderedInterval (-12149737747 / 1000000000000) (-12149712273 / 1000000000000))) = true
  rfl'

theorem compactCertificate557_chunkChecks2 :
    compactCertificate557.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate557.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate557_chunkChecks2_0
    compactCertificate557_chunkChecks2_1 compactCertificate557_chunkChecks2_2

theorem compactCertificate557_chunkChecks3_0 :
    compactCertificate557.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (857 / 2) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34577147156 / 1000000000000) (34577191146 / 1000000000000), orderedInterval (-17073056234 / 1000000000000) (-17073012245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1262524642351157 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34748363097 / 1000000000000) (34748430568 / 1000000000000), orderedInterval (-28507180574 / 1000000000000) (-28507113103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (408274529130581 / 800000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28755458136 / 1000000000000) (28755509197 / 1000000000000), orderedInterval (-20535675116 / 1000000000000) (-20535624055 / 1000000000000)))) (orderedInterval (8947021003 / 1000000000000) (8947043848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (368401541856799 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81356810016 / 1000000000000) (-81356809477 / 1000000000000), orderedInterval (17565159135 / 1000000000000) (17565159673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (989578361390803 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (321427545 / 1000000000000) (321427548 / 1000000000000), orderedInterval (-50727358573 / 1000000000000) (-50727358571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2686897751582151 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6382046068 / 1000000000000) (6382046069 / 1000000000000), orderedInterval (30111843144 / 1000000000000) (30111843145 / 1000000000000)))) (orderedInterval (8602195673 / 1000000000000) (8602195795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1979156722782463 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664237082 / 1000000000000) (-25664223890 / 1000000000000), orderedInterval (25085771715 / 1000000000000) (25085784907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3391318778133499 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10289344779 / 1000000000000) (10289344780 / 1000000000000), orderedInterval (25391001516 / 1000000000000) (25391001517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2498030062694641 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3688226701 / 1000000000000) (-3688226700 / 1000000000000), orderedInterval (-31711274110 / 1000000000000) (-31711274109 / 1000000000000)))) (orderedInterval (8435480432 / 1000000000000) (8435480567 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate557_chunkChecks3_1 :
    compactCertificate557.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3832620513434143 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17657448178 / 1000000000000) (-17657448177 / 1000000000000), orderedInterval (-18769416481 / 1000000000000) (-18769416480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2212764485132647 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29526668217 / 1000000000000) (29526668218 / 1000000000000), orderedInterval (16676277832 / 1000000000000) (16676277834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3926589409175123 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19722731502 / 1000000000000) (19722734049 / 1000000000000), orderedInterval (-16120157472 / 1000000000000) (-16120154925 / 1000000000000)))) (orderedInterval (-12314890902 / 1000000000000) (-12314884890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3668729169833087 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15361411522 / 1000000000000) (15361411523 / 1000000000000), orderedInterval (21395619130 / 1000000000000) (21395619131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2618178247050671 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29721987733 / 1000000000000) (29722019694 / 1000000000000), orderedInterval (-9468200777 / 1000000000000) (-9468168816 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2968735084172409 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29283064981 / 1000000000000) (29283066823 / 1000000000000), orderedInterval (497516702 / 1000000000000) (497518545 / 1000000000000)))) (orderedInterval (7003377038 / 1000000000000) (7003388108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2475021806991721 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19332594303 / 1000000000000) (-19332594302 / 1000000000000), orderedInterval (-25579734153 / 1000000000000) (-25579734152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2186756826358141 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25348141758 / 1000000000000) (25348141759 / 1000000000000), orderedInterval (22823523439 / 1000000000000) (22823523440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (633807361219959 / 800000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27737695110 / 1000000000000) (27737695356 / 1000000000000), orderedInterval (5828003743 / 1000000000000) (5828003989 / 1000000000000)))) (orderedInterval (2657683063 / 1000000000000) (2657683239 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate557_chunkChecks3_2 :
    compactCertificate557.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1753144516588373 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26026768102 / 1000000000000) (-26026756934 / 1000000000000), orderedInterval (27870817395 / 1000000000000) (27870828563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1486160022255853 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41349536563 / 1000000000000) (41349536980 / 1000000000000), orderedInterval (-1973068786 / 1000000000000) (-1973068369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (929969937305359 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (37519239190 / 1000000000000) (37519239191 / 1000000000000), orderedInterval (36395941906 / 1000000000000) (36395941907 / 1000000000000)))) (orderedInterval (4513479392 / 1000000000000) (4513481415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (500140925223153 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11080845214 / 1000000000000) (11080845215 / 1000000000000), orderedInterval (70445240404 / 1000000000000) (70445240405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1357979903248459 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36155251576 / 1000000000000) (36155251577 / 1000000000000), orderedInterval (23779364245 / 1000000000000) (23779364246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1854205460612843 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21508889249 / 1000000000000) (-21508886812 / 1000000000000), orderedInterval (30201357197 / 1000000000000) (30201359633 / 1000000000000)))) (orderedInterval (3234173886 / 1000000000000) (3234174170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (784030062694641 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51495715341 / 1000000000000) (51495728114 / 1000000000000), orderedInterval (-24546924410 / 1000000000000) (-24546911637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3187038676806161 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11516357774 / 1000000000000) (-11516357756 / 1000000000000), orderedInterval (25821654141 / 1000000000000) (25821654160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2128794135783199 / 4000000000000) 3 (IntervalRat.scale (857 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30617859725 / 1000000000000) (-30617772800 / 1000000000000), orderedInterval (16114623429 / 1000000000000) (16114710354 / 1000000000000)))) (orderedInterval (19348067085 / 1000000000000) (19348098788 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate557_chunkChecks3 :
    compactCertificate557.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate557.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate557_chunkChecks3_0
    compactCertificate557_chunkChecks3_1 compactCertificate557_chunkChecks3_2

theorem compactCertificate557_chunkChecks4_0 :
    compactCertificate557.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (857 / 2) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34577147156 / 1000000000000) (34577191146 / 1000000000000), orderedInterval (-17073056234 / 1000000000000) (-17073012245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1262524642351157 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34748363097 / 1000000000000) (34748430568 / 1000000000000), orderedInterval (-28507180574 / 1000000000000) (-28507113103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (408274529130581 / 800000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28755458136 / 1000000000000) (28755509197 / 1000000000000), orderedInterval (-20535675116 / 1000000000000) (-20535624055 / 1000000000000)))) (orderedInterval (17153835691 / 1000000000000) (17153859499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (368401541856799 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81356810016 / 1000000000000) (-81356809477 / 1000000000000), orderedInterval (17565159135 / 1000000000000) (17565159673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (989578361390803 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (321427545 / 1000000000000) (321427548 / 1000000000000), orderedInterval (-50727358573 / 1000000000000) (-50727358571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2686897751582151 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (6382046068 / 1000000000000) (6382046069 / 1000000000000), orderedInterval (30111843144 / 1000000000000) (30111843145 / 1000000000000)))) (orderedInterval (-2776811407 / 1000000000000) (-2776811220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1979156722782463 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25664237082 / 1000000000000) (-25664223890 / 1000000000000), orderedInterval (25085771715 / 1000000000000) (25085784907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3391318778133499 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10289344779 / 1000000000000) (10289344780 / 1000000000000), orderedInterval (25391001516 / 1000000000000) (25391001517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2498030062694641 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-3688226701 / 1000000000000) (-3688226700 / 1000000000000), orderedInterval (-31711274110 / 1000000000000) (-31711274109 / 1000000000000)))) (orderedInterval (-5305486928 / 1000000000000) (-5305486677 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate557_chunkChecks4_1 :
    compactCertificate557.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3832620513434143 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17657448178 / 1000000000000) (-17657448177 / 1000000000000), orderedInterval (-18769416481 / 1000000000000) (-18769416480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2212764485132647 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29526668217 / 1000000000000) (29526668218 / 1000000000000), orderedInterval (16676277832 / 1000000000000) (16676277834 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3926589409175123 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19722731502 / 1000000000000) (19722734049 / 1000000000000), orderedInterval (-16120157472 / 1000000000000) (-16120154925 / 1000000000000)))) (orderedInterval (161795775464 / 1000000000000) (161795789132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3668729169833087 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15361411522 / 1000000000000) (15361411523 / 1000000000000), orderedInterval (21395619130 / 1000000000000) (21395619131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2618178247050671 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29721987733 / 1000000000000) (29722019694 / 1000000000000), orderedInterval (-9468200777 / 1000000000000) (-9468168816 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2968735084172409 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29283064981 / 1000000000000) (29283066823 / 1000000000000), orderedInterval (497516702 / 1000000000000) (497518545 / 1000000000000)))) (orderedInterval (8114660680 / 1000000000000) (8114677673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2475021806991721 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19332594303 / 1000000000000) (-19332594302 / 1000000000000), orderedInterval (-25579734153 / 1000000000000) (-25579734152 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2186756826358141 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25348141758 / 1000000000000) (25348141759 / 1000000000000), orderedInterval (22823523439 / 1000000000000) (22823523440 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (633807361219959 / 800000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27737695110 / 1000000000000) (27737695356 / 1000000000000), orderedInterval (5828003743 / 1000000000000) (5828003989 / 1000000000000)))) (orderedInterval (3473000921 / 1000000000000) (3473001210 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate557_chunkChecks4_2 :
    compactCertificate557.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1753144516588373 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26026768102 / 1000000000000) (-26026756934 / 1000000000000), orderedInterval (27870817395 / 1000000000000) (27870828563 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1486160022255853 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41349536563 / 1000000000000) (41349536980 / 1000000000000), orderedInterval (-1973068786 / 1000000000000) (-1973068369 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (929969937305359 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (37519239190 / 1000000000000) (37519239191 / 1000000000000), orderedInterval (36395941906 / 1000000000000) (36395941907 / 1000000000000)))) (orderedInterval (3316802219 / 1000000000000) (3316804287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (500140925223153 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (11080845214 / 1000000000000) (11080845215 / 1000000000000), orderedInterval (70445240404 / 1000000000000) (70445240405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1357979903248459 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36155251576 / 1000000000000) (36155251577 / 1000000000000), orderedInterval (23779364245 / 1000000000000) (23779364246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1854205460612843 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-21508889249 / 1000000000000) (-21508886812 / 1000000000000), orderedInterval (30201357197 / 1000000000000) (30201359633 / 1000000000000)))) (orderedInterval (1917852887 / 1000000000000) (1917853194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (784030062694641 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51495715341 / 1000000000000) (51495728114 / 1000000000000), orderedInterval (-24546924410 / 1000000000000) (-24546911637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3187038676806161 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11516357774 / 1000000000000) (-11516357756 / 1000000000000), orderedInterval (25821654141 / 1000000000000) (25821654160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2128794135783199 / 4000000000000) 4 (IntervalRat.scale (857 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30617859725 / 1000000000000) (-30617772800 / 1000000000000), orderedInterval (16114623429 / 1000000000000) (16114710354 / 1000000000000)))) (orderedInterval (24799041832 / 1000000000000) (24799081416 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate557_chunkChecks4 :
    compactCertificate557.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate557.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate557_chunkChecks4_0
    compactCertificate557_chunkChecks4_1 compactCertificate557_chunkChecks4_2

theorem compactCertificate557_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate557.chunkCheck r b = true :=
  compactCertificate557.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate557_chunkChecks0
    · exact compactCertificate557_chunkChecks1
    · exact compactCertificate557_chunkChecks2
    · exact compactCertificate557_chunkChecks3
    · exact compactCertificate557_chunkChecks4)

theorem compactCertificate557_coefficient0 :
    compactCertificate557.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate557_coefficient1 :
    compactCertificate557.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate557_coefficient2 :
    compactCertificate557.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate557_coefficient3 :
    compactCertificate557.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate557_coefficient4 :
    compactCertificate557.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate557_coefficients : ∀ r : Fin 5,
    compactCertificate557.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate557_coefficient0
  · exact compactCertificate557_coefficient1
  · exact compactCertificate557_coefficient2
  · exact compactCertificate557_coefficient3
  · exact compactCertificate557_coefficient4

theorem compactCertificate557_lower : (1 : ℚ) ≤ compactCertificate557.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate557, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate557_proves {t : ℝ} (ht : t ∈ compactCertificate557.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate557.proves compactCertificate557_states compactCertificate557_chunks
    compactCertificate557_coefficients compactCertificate557_lower ht

end Erdos232
