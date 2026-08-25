/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate456 : CompactCertificate where
  left := 327
  right := 328
  center := 655 / 2
  grid := fun i =>
    match i.val with
    | 0 => 104
    | 1 => 77
    | 2 => 124
    | 3 => 22
    | 4 => 60
    | 5 => 164
    | 6 => 120
    | 7 => 206
    | 8 => 152
    | 9 => 233
    | 10 => 135
    | 11 => 239
    | 12 => 223
    | 13 => 159
    | 14 => 181
    | 15 => 151
    | 16 => 133
    | 17 => 193
    | 18 => 107
    | 19 => 90
    | 20 => 57
    | 21 => 30
    | 22 => 83
    | 23 => 113
    | 24 => 48
    | 25 => 194
    | _ => 130
  point := fun i =>
    match i.val with
    | 0 => 655 / 2
    | 1 => 192988014175031 / 800000000000
    | 2 => 62408358595223 / 160000000000
    | 3 => 56313421217317 / 800000000000
    | 4 => 151265770527649 / 800000000000
    | 5 => 410715992365533 / 800000000000
    | 6 => 302531541055429 / 800000000000
    | 7 => 518392952083417 / 800000000000
    | 8 => 381845902232203 / 800000000000
    | 9 => 585849810104869 / 800000000000
    | 10 => 338240545568701 / 800000000000
    | 11 => 600213783666209 / 800000000000
    | 12 => 560797574385221 / 800000000000
    | 13 => 400211610692693 / 800000000000
    | 14 => 453797311582947 / 800000000000
    | 15 => 378328887649843 / 800000000000
    | 16 => 334265045802703 / 800000000000
    | 17 => 96883038879597 / 160000000000
    | 18 => 267983584215959 / 800000000000
    | 19 => 227172652176799 / 800000000000
    | 20 => 142154097767797 / 800000000000
    | 21 => 76450946562699 / 800000000000
    | 22 => 207579191745097 / 800000000000
    | 23 => 283431639836969 / 800000000000
    | 24 => 119845902232203 / 800000000000
    | 25 => 487166938928363 / 800000000000
    | _ => 325404937908517 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (44086523782 / 1000000000000) (44086523926 / 1000000000000), orderedInterval (435998435 / 1000000000000) (435998580 / 1000000000000))
    | 1 => (orderedInterval (-6010161089 / 1000000000000) (-6010161088 / 1000000000000), orderedInterval (-51006027881 / 1000000000000) (-51006027880 / 1000000000000))
    | 2 => (orderedInterval (38701613688 / 1000000000000) (38701613692 / 1000000000000), orderedInterval (11540201181 / 1000000000000) (11540201185 / 1000000000000))
    | 3 => (orderedInterval (83928005095 / 1000000000000) (83928016033 / 1000000000000), orderedInterval (-45316507853 / 1000000000000) (-45316496915 / 1000000000000))
    | 4 => (orderedInterval (56875053496 / 1000000000000) (56875053499 / 1000000000000), orderedInterval (11343578317 / 1000000000000) (11343578321 / 1000000000000))
    | 5 => (orderedInterval (-30387371394 / 1000000000000) (-30387262883 / 1000000000000), orderedInterval (17823639891 / 1000000000000) (17823748402 / 1000000000000))
    | 6 => (orderedInterval (37986487413 / 1000000000000) (37986505657 / 1000000000000), orderedInterval (-15557393827 / 1000000000000) (-15557375583 / 1000000000000))
    | 7 => (orderedInterval (31322022338 / 1000000000000) (31322024342 / 1000000000000), orderedInterval (-1199685516 / 1000000000000) (-1199683512 / 1000000000000))
    | 8 => (orderedInterval (19721062313 / 1000000000000) (19721062314 / 1000000000000), orderedInterval (30717805411 / 1000000000000) (30717805412 / 1000000000000))
    | 9 => (orderedInterval (-26361766688 / 1000000000000) (-26361766684 / 1000000000000), orderedInterval (-13187508701 / 1000000000000) (-13187508697 / 1000000000000))
    | 10 => (orderedInterval (19590520753 / 1000000000000) (19590521854 / 1000000000000), orderedInterval (-33518432956 / 1000000000000) (-33518431855 / 1000000000000))
    | 11 => (orderedInterval (-6124071971 / 1000000000000) (-6124071970 / 1000000000000), orderedInterval (-28474330621 / 1000000000000) (-28474330620 / 1000000000000))
    | 12 => (orderedInterval (-28163722793 / 1000000000000) (-28163722780 / 1000000000000), orderedInterval (-10702221198 / 1000000000000) (-10702221185 / 1000000000000))
    | 13 => (orderedInterval (-35651974864 / 1000000000000) (-35651974523 / 1000000000000), orderedInterval (-1190086927 / 1000000000000) (-1190086585 / 1000000000000))
    | 14 => (orderedInterval (18817732819 / 1000000000000) (18817733845 / 1000000000000), orderedInterval (-27732847581 / 1000000000000) (-27732846555 / 1000000000000))
    | 15 => (orderedInterval (23191508516 / 1000000000000) (23191513199 / 1000000000000), orderedInterval (-28455599183 / 1000000000000) (-28455594500 / 1000000000000))
    | 16 => (orderedInterval (-27578475267 / 1000000000000) (-27578475266 / 1000000000000), orderedInterval (-27590473751 / 1000000000000) (-27590473750 / 1000000000000))
    | 17 => (orderedInterval (752102036 / 1000000000000) (752102037 / 1000000000000), orderedInterval (-32416618432 / 1000000000000) (-32416618431 / 1000000000000))
    | 18 => (orderedInterval (16408981415 / 1000000000000) (16408981739 / 1000000000000), orderedInterval (-40412866934 / 1000000000000) (-40412866610 / 1000000000000))
    | 19 => (orderedInterval (42906231262 / 1000000000000) (42906249749 / 1000000000000), orderedInterval (-20099069060 / 1000000000000) (-20099050573 / 1000000000000))
    | 20 => (orderedInterval (33473399796 / 1000000000000) (33473408366 / 1000000000000), orderedInterval (-49715144191 / 1000000000000) (-49715135621 / 1000000000000))
    | 21 => (orderedInterval (70454430510 / 1000000000000) (70454448625 / 1000000000000), orderedInterval (-41573726864 / 1000000000000) (-41573708748 / 1000000000000))
    | 22 => (orderedInterval (23454815315 / 1000000000000) (23454817205 / 1000000000000), orderedInterval (-43672888469 / 1000000000000) (-43672886579 / 1000000000000))
    | 23 => (orderedInterval (-3160410666 / 1000000000000) (-3160410665 / 1000000000000), orderedInterval (-42267336173 / 1000000000000) (-42267336172 / 1000000000000))
    | 24 => (orderedInterval (-13238733414 / 1000000000000) (-13238733315 / 1000000000000), orderedInterval (63874793732 / 1000000000000) (63874793831 / 1000000000000))
    | 25 => (orderedInterval (8776560345 / 1000000000000) (8776560346 / 1000000000000), orderedInterval (31111853792 / 1000000000000) (31111853793 / 1000000000000))
    | _ => (orderedInterval (-30130144423 / 1000000000000) (-30130106363 / 1000000000000), orderedInterval (25674671518 / 1000000000000) (25674709577 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (19689406448 / 1000000000000) (19689406529 / 1000000000000)
      | 1 => orderedInterval (3326267627 / 1000000000000) (3326275500 / 1000000000000)
      | 2 => orderedInterval (-489477393 / 1000000000000) (-489477312 / 1000000000000)
      | 3 => orderedInterval (5265091046 / 1000000000000) (5265091259 / 1000000000000)
      | 4 => orderedInterval (-2958139404 / 1000000000000) (-2958139327 / 1000000000000)
      | 5 => orderedInterval (1865289150 / 1000000000000) (1865289236 / 1000000000000)
      | 6 => orderedInterval (-3962428449 / 1000000000000) (-3962426989 / 1000000000000)
      | 7 => orderedInterval (-1590855556 / 1000000000000) (-1590855139 / 1000000000000)
      | _ => orderedInterval (4858972134 / 1000000000000) (4858979367 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (629262777 / 1000000000000) (629262861 / 1000000000000)
      | 1 => orderedInterval (-1641506458 / 1000000000000) (-1641494295 / 1000000000000)
      | 2 => orderedInterval (1155191652 / 1000000000000) (1155191807 / 1000000000000)
      | 3 => orderedInterval (-7239476246 / 1000000000000) (-7239475869 / 1000000000000)
      | 4 => orderedInterval (484730612 / 1000000000000) (484730735 / 1000000000000)
      | 5 => orderedInterval (5328373 / 1000000000000) (5328497 / 1000000000000)
      | 6 => orderedInterval (6717521220 / 1000000000000) (6717522408 / 1000000000000)
      | 7 => orderedInterval (4513298615 / 1000000000000) (4513298783 / 1000000000000)
      | _ => orderedInterval (-10515996346 / 1000000000000) (-10515987349 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-20667334269 / 1000000000000) (-20667334181 / 1000000000000)
      | 1 => orderedInterval (-5953725687 / 1000000000000) (-5953706625 / 1000000000000)
      | 2 => orderedInterval (2766215774 / 1000000000000) (2766216074 / 1000000000000)
      | 3 => orderedInterval (-21248964100 / 1000000000000) (-21248963383 / 1000000000000)
      | 4 => orderedInterval (5821257487 / 1000000000000) (5821257685 / 1000000000000)
      | 5 => orderedInterval (-3193169303 / 1000000000000) (-3193169122 / 1000000000000)
      | 6 => orderedInterval (4229335770 / 1000000000000) (4229336769 / 1000000000000)
      | 7 => orderedInterval (147551842 / 1000000000000) (147551934 / 1000000000000)
      | _ => orderedInterval (-6201605179 / 1000000000000) (-6201593948 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-1063808137 / 1000000000000) (-1063808044 / 1000000000000)
      | 1 => orderedInterval (4814741435 / 1000000000000) (4814771303 / 1000000000000)
      | 2 => orderedInterval (-2593280708 / 1000000000000) (-2593280124 / 1000000000000)
      | 3 => orderedInterval (27876628129 / 1000000000000) (27876629578 / 1000000000000)
      | 4 => orderedInterval (-2240606849 / 1000000000000) (-2240606526 / 1000000000000)
      | 5 => orderedInterval (2966198405 / 1000000000000) (2966198673 / 1000000000000)
      | 6 => orderedInterval (-7410534073 / 1000000000000) (-7410533217 / 1000000000000)
      | 7 => orderedInterval (-4613289803 / 1000000000000) (-4613289736 / 1000000000000)
      | _ => orderedInterval (25492569489 / 1000000000000) (25492583494 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (22033722819 / 1000000000000) (22033722917 / 1000000000000)
      | 1 => orderedInterval (13244785969 / 1000000000000) (13244832878 / 1000000000000)
      | 2 => orderedInterval (-12640215801 / 1000000000000) (-12640214659 / 1000000000000)
      | 3 => orderedInterval (96987086160 / 1000000000000) (96987089215 / 1000000000000)
      | 4 => orderedInterval (-8526094145 / 1000000000000) (-8526093608 / 1000000000000)
      | 5 => orderedInterval (5552730108 / 1000000000000) (5552730509 / 1000000000000)
      | 6 => orderedInterval (-4104590525 / 1000000000000) (-4104589778 / 1000000000000)
      | 7 => orderedInterval (140799177 / 1000000000000) (140799234 / 1000000000000)
      | _ => orderedInterval (4752624507 / 1000000000000) (4752642049 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (26004125603 / 1000000000000) (26004143124 / 1000000000000)
    | 1 => orderedInterval (-5891645801 / 1000000000000) (-5891622422 / 1000000000000)
    | 2 => orderedInterval (-44300437665 / 1000000000000) (-44300404797 / 1000000000000)
    | 3 => orderedInterval (43228617888 / 1000000000000) (43228665401 / 1000000000000)
    | _ => orderedInterval (117440848269 / 1000000000000) (117440918757 / 1000000000000)

theorem compactCertificate456_stateChecks0 :
    compactCertificate456.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (655 / 2)) (orderedInterval (44086523782 / 1000000000000) (44086523926 / 1000000000000), orderedInterval (435998435 / 1000000000000) (435998580 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (192988014175031 / 800000000000)) (orderedInterval (-6010161089 / 1000000000000) (-6010161088 / 1000000000000), orderedInterval (-51006027881 / 1000000000000) (-51006027880 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (62408358595223 / 160000000000)) (orderedInterval (38701613688 / 1000000000000) (38701613692 / 1000000000000), orderedInterval (11540201181 / 1000000000000) (11540201185 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks1 :
    compactCertificate456.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (56313421217317 / 800000000000)) (orderedInterval (83928005095 / 1000000000000) (83928016033 / 1000000000000), orderedInterval (-45316507853 / 1000000000000) (-45316496915 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (151265770527649 / 800000000000)) (orderedInterval (56875053496 / 1000000000000) (56875053499 / 1000000000000), orderedInterval (11343578317 / 1000000000000) (11343578321 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (410715992365533 / 800000000000)) (orderedInterval (-30387371394 / 1000000000000) (-30387262883 / 1000000000000), orderedInterval (17823639891 / 1000000000000) (17823748402 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks2 :
    compactCertificate456.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (302531541055429 / 800000000000)) (orderedInterval (37986487413 / 1000000000000) (37986505657 / 1000000000000), orderedInterval (-15557393827 / 1000000000000) (-15557375583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (518392952083417 / 800000000000)) (orderedInterval (31322022338 / 1000000000000) (31322024342 / 1000000000000), orderedInterval (-1199685516 / 1000000000000) (-1199683512 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (381845902232203 / 800000000000)) (orderedInterval (19721062313 / 1000000000000) (19721062314 / 1000000000000), orderedInterval (30717805411 / 1000000000000) (30717805412 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks3 :
    compactCertificate456.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (585849810104869 / 800000000000)) (orderedInterval (-26361766688 / 1000000000000) (-26361766684 / 1000000000000), orderedInterval (-13187508701 / 1000000000000) (-13187508697 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (338240545568701 / 800000000000)) (orderedInterval (19590520753 / 1000000000000) (19590521854 / 1000000000000), orderedInterval (-33518432956 / 1000000000000) (-33518431855 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (600213783666209 / 800000000000)) (orderedInterval (-6124071971 / 1000000000000) (-6124071970 / 1000000000000), orderedInterval (-28474330621 / 1000000000000) (-28474330620 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks4 :
    compactCertificate456.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (560797574385221 / 800000000000)) (orderedInterval (-28163722793 / 1000000000000) (-28163722780 / 1000000000000), orderedInterval (-10702221198 / 1000000000000) (-10702221185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (400211610692693 / 800000000000)) (orderedInterval (-35651974864 / 1000000000000) (-35651974523 / 1000000000000), orderedInterval (-1190086927 / 1000000000000) (-1190086585 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (453797311582947 / 800000000000)) (orderedInterval (18817732819 / 1000000000000) (18817733845 / 1000000000000), orderedInterval (-27732847581 / 1000000000000) (-27732846555 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks5 :
    compactCertificate456.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (378328887649843 / 800000000000)) (orderedInterval (23191508516 / 1000000000000) (23191513199 / 1000000000000), orderedInterval (-28455599183 / 1000000000000) (-28455594500 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (334265045802703 / 800000000000)) (orderedInterval (-27578475267 / 1000000000000) (-27578475266 / 1000000000000), orderedInterval (-27590473751 / 1000000000000) (-27590473750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (96883038879597 / 160000000000)) (orderedInterval (752102036 / 1000000000000) (752102037 / 1000000000000), orderedInterval (-32416618432 / 1000000000000) (-32416618431 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks6 :
    compactCertificate456.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (267983584215959 / 800000000000)) (orderedInterval (16408981415 / 1000000000000) (16408981739 / 1000000000000), orderedInterval (-40412866934 / 1000000000000) (-40412866610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (227172652176799 / 800000000000)) (orderedInterval (42906231262 / 1000000000000) (42906249749 / 1000000000000), orderedInterval (-20099069060 / 1000000000000) (-20099050573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (142154097767797 / 800000000000)) (orderedInterval (33473399796 / 1000000000000) (33473408366 / 1000000000000), orderedInterval (-49715144191 / 1000000000000) (-49715135621 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks7 :
    compactCertificate456.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (76450946562699 / 800000000000)) (orderedInterval (70454430510 / 1000000000000) (70454448625 / 1000000000000), orderedInterval (-41573726864 / 1000000000000) (-41573708748 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (207579191745097 / 800000000000)) (orderedInterval (23454815315 / 1000000000000) (23454817205 / 1000000000000), orderedInterval (-43672888469 / 1000000000000) (-43672886579 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (283431639836969 / 800000000000)) (orderedInterval (-3160410666 / 1000000000000) (-3160410665 / 1000000000000), orderedInterval (-42267336173 / 1000000000000) (-42267336172 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_stateChecks8 :
    compactCertificate456.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (119845902232203 / 800000000000)) (orderedInterval (-13238733414 / 1000000000000) (-13238733315 / 1000000000000), orderedInterval (63874793732 / 1000000000000) (63874793831 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (487166938928363 / 800000000000)) (orderedInterval (8776560345 / 1000000000000) (8776560346 / 1000000000000), orderedInterval (31111853792 / 1000000000000) (31111853793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (325404937908517 / 800000000000)) (orderedInterval (-30130144423 / 1000000000000) (-30130106363 / 1000000000000), orderedInterval (25674671518 / 1000000000000) (25674709577 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_states : ∀ j,
    BesselStateValid (compactCertificate456.point j) (compactCertificate456.state j) :=
  compactCertificate456.statesValid_of_checks3 compactCertificate456_stateChecks0
    compactCertificate456_stateChecks1 compactCertificate456_stateChecks2
    compactCertificate456_stateChecks3 compactCertificate456_stateChecks4
    compactCertificate456_stateChecks5 compactCertificate456_stateChecks6
    compactCertificate456_stateChecks7 compactCertificate456_stateChecks8

theorem compactCertificate456_chunkChecks0_0 :
    compactCertificate456.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (655 / 2) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44086523782 / 1000000000000) (44086523926 / 1000000000000), orderedInterval (435998435 / 1000000000000) (435998580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (192988014175031 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6010161089 / 1000000000000) (-6010161088 / 1000000000000), orderedInterval (-51006027881 / 1000000000000) (-51006027880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (62408358595223 / 160000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38701613688 / 1000000000000) (38701613692 / 1000000000000), orderedInterval (11540201181 / 1000000000000) (11540201185 / 1000000000000)))) (orderedInterval (19689406448 / 1000000000000) (19689406529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (56313421217317 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83928005095 / 1000000000000) (83928016033 / 1000000000000), orderedInterval (-45316507853 / 1000000000000) (-45316496915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (151265770527649 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56875053496 / 1000000000000) (56875053499 / 1000000000000), orderedInterval (11343578317 / 1000000000000) (11343578321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (410715992365533 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30387371394 / 1000000000000) (-30387262883 / 1000000000000), orderedInterval (17823639891 / 1000000000000) (17823748402 / 1000000000000)))) (orderedInterval (3326267627 / 1000000000000) (3326275500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (302531541055429 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37986487413 / 1000000000000) (37986505657 / 1000000000000), orderedInterval (-15557393827 / 1000000000000) (-15557375583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (518392952083417 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31322022338 / 1000000000000) (31322024342 / 1000000000000), orderedInterval (-1199685516 / 1000000000000) (-1199683512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (381845902232203 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19721062313 / 1000000000000) (19721062314 / 1000000000000), orderedInterval (30717805411 / 1000000000000) (30717805412 / 1000000000000)))) (orderedInterval (-489477393 / 1000000000000) (-489477312 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks0_1 :
    compactCertificate456.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (585849810104869 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26361766688 / 1000000000000) (-26361766684 / 1000000000000), orderedInterval (-13187508701 / 1000000000000) (-13187508697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (338240545568701 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19590520753 / 1000000000000) (19590521854 / 1000000000000), orderedInterval (-33518432956 / 1000000000000) (-33518431855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (600213783666209 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6124071971 / 1000000000000) (-6124071970 / 1000000000000), orderedInterval (-28474330621 / 1000000000000) (-28474330620 / 1000000000000)))) (orderedInterval (5265091046 / 1000000000000) (5265091259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (560797574385221 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28163722793 / 1000000000000) (-28163722780 / 1000000000000), orderedInterval (-10702221198 / 1000000000000) (-10702221185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (400211610692693 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35651974864 / 1000000000000) (-35651974523 / 1000000000000), orderedInterval (-1190086927 / 1000000000000) (-1190086585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (453797311582947 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18817732819 / 1000000000000) (18817733845 / 1000000000000), orderedInterval (-27732847581 / 1000000000000) (-27732846555 / 1000000000000)))) (orderedInterval (-2958139404 / 1000000000000) (-2958139327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (378328887649843 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23191508516 / 1000000000000) (23191513199 / 1000000000000), orderedInterval (-28455599183 / 1000000000000) (-28455594500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (334265045802703 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27578475267 / 1000000000000) (-27578475266 / 1000000000000), orderedInterval (-27590473751 / 1000000000000) (-27590473750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (96883038879597 / 160000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (752102036 / 1000000000000) (752102037 / 1000000000000), orderedInterval (-32416618432 / 1000000000000) (-32416618431 / 1000000000000)))) (orderedInterval (1865289150 / 1000000000000) (1865289236 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks0_2 :
    compactCertificate456.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (267983584215959 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16408981415 / 1000000000000) (16408981739 / 1000000000000), orderedInterval (-40412866934 / 1000000000000) (-40412866610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (227172652176799 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42906231262 / 1000000000000) (42906249749 / 1000000000000), orderedInterval (-20099069060 / 1000000000000) (-20099050573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (142154097767797 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33473399796 / 1000000000000) (33473408366 / 1000000000000), orderedInterval (-49715144191 / 1000000000000) (-49715135621 / 1000000000000)))) (orderedInterval (-3962428449 / 1000000000000) (-3962426989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (76450946562699 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70454430510 / 1000000000000) (70454448625 / 1000000000000), orderedInterval (-41573726864 / 1000000000000) (-41573708748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (207579191745097 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23454815315 / 1000000000000) (23454817205 / 1000000000000), orderedInterval (-43672888469 / 1000000000000) (-43672886579 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (283431639836969 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3160410666 / 1000000000000) (-3160410665 / 1000000000000), orderedInterval (-42267336173 / 1000000000000) (-42267336172 / 1000000000000)))) (orderedInterval (-1590855556 / 1000000000000) (-1590855139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (119845902232203 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13238733414 / 1000000000000) (-13238733315 / 1000000000000), orderedInterval (63874793732 / 1000000000000) (63874793831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (487166938928363 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8776560345 / 1000000000000) (8776560346 / 1000000000000), orderedInterval (31111853792 / 1000000000000) (31111853793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (325404937908517 / 800000000000) 0 (IntervalRat.scale (655 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30130144423 / 1000000000000) (-30130106363 / 1000000000000), orderedInterval (25674671518 / 1000000000000) (25674709577 / 1000000000000)))) (orderedInterval (4858972134 / 1000000000000) (4858979367 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks0 :
    compactCertificate456.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate456.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate456_chunkChecks0_0
    compactCertificate456_chunkChecks0_1 compactCertificate456_chunkChecks0_2

theorem compactCertificate456_chunkChecks1_0 :
    compactCertificate456.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (655 / 2) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44086523782 / 1000000000000) (44086523926 / 1000000000000), orderedInterval (435998435 / 1000000000000) (435998580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (192988014175031 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6010161089 / 1000000000000) (-6010161088 / 1000000000000), orderedInterval (-51006027881 / 1000000000000) (-51006027880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (62408358595223 / 160000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38701613688 / 1000000000000) (38701613692 / 1000000000000), orderedInterval (11540201181 / 1000000000000) (11540201185 / 1000000000000)))) (orderedInterval (629262777 / 1000000000000) (629262861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (56313421217317 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83928005095 / 1000000000000) (83928016033 / 1000000000000), orderedInterval (-45316507853 / 1000000000000) (-45316496915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (151265770527649 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56875053496 / 1000000000000) (56875053499 / 1000000000000), orderedInterval (11343578317 / 1000000000000) (11343578321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (410715992365533 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30387371394 / 1000000000000) (-30387262883 / 1000000000000), orderedInterval (17823639891 / 1000000000000) (17823748402 / 1000000000000)))) (orderedInterval (-1641506458 / 1000000000000) (-1641494295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (302531541055429 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37986487413 / 1000000000000) (37986505657 / 1000000000000), orderedInterval (-15557393827 / 1000000000000) (-15557375583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (518392952083417 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31322022338 / 1000000000000) (31322024342 / 1000000000000), orderedInterval (-1199685516 / 1000000000000) (-1199683512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (381845902232203 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19721062313 / 1000000000000) (19721062314 / 1000000000000), orderedInterval (30717805411 / 1000000000000) (30717805412 / 1000000000000)))) (orderedInterval (1155191652 / 1000000000000) (1155191807 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks1_1 :
    compactCertificate456.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (585849810104869 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26361766688 / 1000000000000) (-26361766684 / 1000000000000), orderedInterval (-13187508701 / 1000000000000) (-13187508697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (338240545568701 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19590520753 / 1000000000000) (19590521854 / 1000000000000), orderedInterval (-33518432956 / 1000000000000) (-33518431855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (600213783666209 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6124071971 / 1000000000000) (-6124071970 / 1000000000000), orderedInterval (-28474330621 / 1000000000000) (-28474330620 / 1000000000000)))) (orderedInterval (-7239476246 / 1000000000000) (-7239475869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (560797574385221 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28163722793 / 1000000000000) (-28163722780 / 1000000000000), orderedInterval (-10702221198 / 1000000000000) (-10702221185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (400211610692693 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35651974864 / 1000000000000) (-35651974523 / 1000000000000), orderedInterval (-1190086927 / 1000000000000) (-1190086585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (453797311582947 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18817732819 / 1000000000000) (18817733845 / 1000000000000), orderedInterval (-27732847581 / 1000000000000) (-27732846555 / 1000000000000)))) (orderedInterval (484730612 / 1000000000000) (484730735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (378328887649843 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23191508516 / 1000000000000) (23191513199 / 1000000000000), orderedInterval (-28455599183 / 1000000000000) (-28455594500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (334265045802703 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27578475267 / 1000000000000) (-27578475266 / 1000000000000), orderedInterval (-27590473751 / 1000000000000) (-27590473750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (96883038879597 / 160000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (752102036 / 1000000000000) (752102037 / 1000000000000), orderedInterval (-32416618432 / 1000000000000) (-32416618431 / 1000000000000)))) (orderedInterval (5328373 / 1000000000000) (5328497 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks1_2 :
    compactCertificate456.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (267983584215959 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16408981415 / 1000000000000) (16408981739 / 1000000000000), orderedInterval (-40412866934 / 1000000000000) (-40412866610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (227172652176799 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42906231262 / 1000000000000) (42906249749 / 1000000000000), orderedInterval (-20099069060 / 1000000000000) (-20099050573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (142154097767797 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33473399796 / 1000000000000) (33473408366 / 1000000000000), orderedInterval (-49715144191 / 1000000000000) (-49715135621 / 1000000000000)))) (orderedInterval (6717521220 / 1000000000000) (6717522408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (76450946562699 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70454430510 / 1000000000000) (70454448625 / 1000000000000), orderedInterval (-41573726864 / 1000000000000) (-41573708748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (207579191745097 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23454815315 / 1000000000000) (23454817205 / 1000000000000), orderedInterval (-43672888469 / 1000000000000) (-43672886579 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (283431639836969 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3160410666 / 1000000000000) (-3160410665 / 1000000000000), orderedInterval (-42267336173 / 1000000000000) (-42267336172 / 1000000000000)))) (orderedInterval (4513298615 / 1000000000000) (4513298783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (119845902232203 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13238733414 / 1000000000000) (-13238733315 / 1000000000000), orderedInterval (63874793732 / 1000000000000) (63874793831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (487166938928363 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8776560345 / 1000000000000) (8776560346 / 1000000000000), orderedInterval (31111853792 / 1000000000000) (31111853793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (325404937908517 / 800000000000) 1 (IntervalRat.scale (655 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30130144423 / 1000000000000) (-30130106363 / 1000000000000), orderedInterval (25674671518 / 1000000000000) (25674709577 / 1000000000000)))) (orderedInterval (-10515996346 / 1000000000000) (-10515987349 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks1 :
    compactCertificate456.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate456.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate456_chunkChecks1_0
    compactCertificate456_chunkChecks1_1 compactCertificate456_chunkChecks1_2

theorem compactCertificate456_chunkChecks2_0 :
    compactCertificate456.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (655 / 2) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44086523782 / 1000000000000) (44086523926 / 1000000000000), orderedInterval (435998435 / 1000000000000) (435998580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (192988014175031 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6010161089 / 1000000000000) (-6010161088 / 1000000000000), orderedInterval (-51006027881 / 1000000000000) (-51006027880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (62408358595223 / 160000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38701613688 / 1000000000000) (38701613692 / 1000000000000), orderedInterval (11540201181 / 1000000000000) (11540201185 / 1000000000000)))) (orderedInterval (-20667334269 / 1000000000000) (-20667334181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (56313421217317 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83928005095 / 1000000000000) (83928016033 / 1000000000000), orderedInterval (-45316507853 / 1000000000000) (-45316496915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (151265770527649 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56875053496 / 1000000000000) (56875053499 / 1000000000000), orderedInterval (11343578317 / 1000000000000) (11343578321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (410715992365533 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30387371394 / 1000000000000) (-30387262883 / 1000000000000), orderedInterval (17823639891 / 1000000000000) (17823748402 / 1000000000000)))) (orderedInterval (-5953725687 / 1000000000000) (-5953706625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (302531541055429 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37986487413 / 1000000000000) (37986505657 / 1000000000000), orderedInterval (-15557393827 / 1000000000000) (-15557375583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (518392952083417 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31322022338 / 1000000000000) (31322024342 / 1000000000000), orderedInterval (-1199685516 / 1000000000000) (-1199683512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (381845902232203 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19721062313 / 1000000000000) (19721062314 / 1000000000000), orderedInterval (30717805411 / 1000000000000) (30717805412 / 1000000000000)))) (orderedInterval (2766215774 / 1000000000000) (2766216074 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks2_1 :
    compactCertificate456.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (585849810104869 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26361766688 / 1000000000000) (-26361766684 / 1000000000000), orderedInterval (-13187508701 / 1000000000000) (-13187508697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (338240545568701 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19590520753 / 1000000000000) (19590521854 / 1000000000000), orderedInterval (-33518432956 / 1000000000000) (-33518431855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (600213783666209 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6124071971 / 1000000000000) (-6124071970 / 1000000000000), orderedInterval (-28474330621 / 1000000000000) (-28474330620 / 1000000000000)))) (orderedInterval (-21248964100 / 1000000000000) (-21248963383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (560797574385221 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28163722793 / 1000000000000) (-28163722780 / 1000000000000), orderedInterval (-10702221198 / 1000000000000) (-10702221185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (400211610692693 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35651974864 / 1000000000000) (-35651974523 / 1000000000000), orderedInterval (-1190086927 / 1000000000000) (-1190086585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (453797311582947 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18817732819 / 1000000000000) (18817733845 / 1000000000000), orderedInterval (-27732847581 / 1000000000000) (-27732846555 / 1000000000000)))) (orderedInterval (5821257487 / 1000000000000) (5821257685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (378328887649843 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23191508516 / 1000000000000) (23191513199 / 1000000000000), orderedInterval (-28455599183 / 1000000000000) (-28455594500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (334265045802703 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27578475267 / 1000000000000) (-27578475266 / 1000000000000), orderedInterval (-27590473751 / 1000000000000) (-27590473750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (96883038879597 / 160000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (752102036 / 1000000000000) (752102037 / 1000000000000), orderedInterval (-32416618432 / 1000000000000) (-32416618431 / 1000000000000)))) (orderedInterval (-3193169303 / 1000000000000) (-3193169122 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks2_2 :
    compactCertificate456.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (267983584215959 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16408981415 / 1000000000000) (16408981739 / 1000000000000), orderedInterval (-40412866934 / 1000000000000) (-40412866610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (227172652176799 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42906231262 / 1000000000000) (42906249749 / 1000000000000), orderedInterval (-20099069060 / 1000000000000) (-20099050573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (142154097767797 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33473399796 / 1000000000000) (33473408366 / 1000000000000), orderedInterval (-49715144191 / 1000000000000) (-49715135621 / 1000000000000)))) (orderedInterval (4229335770 / 1000000000000) (4229336769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (76450946562699 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70454430510 / 1000000000000) (70454448625 / 1000000000000), orderedInterval (-41573726864 / 1000000000000) (-41573708748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (207579191745097 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23454815315 / 1000000000000) (23454817205 / 1000000000000), orderedInterval (-43672888469 / 1000000000000) (-43672886579 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (283431639836969 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3160410666 / 1000000000000) (-3160410665 / 1000000000000), orderedInterval (-42267336173 / 1000000000000) (-42267336172 / 1000000000000)))) (orderedInterval (147551842 / 1000000000000) (147551934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (119845902232203 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13238733414 / 1000000000000) (-13238733315 / 1000000000000), orderedInterval (63874793732 / 1000000000000) (63874793831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (487166938928363 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8776560345 / 1000000000000) (8776560346 / 1000000000000), orderedInterval (31111853792 / 1000000000000) (31111853793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (325404937908517 / 800000000000) 2 (IntervalRat.scale (655 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30130144423 / 1000000000000) (-30130106363 / 1000000000000), orderedInterval (25674671518 / 1000000000000) (25674709577 / 1000000000000)))) (orderedInterval (-6201605179 / 1000000000000) (-6201593948 / 1000000000000))) = true
  rfl'

theorem compactCertificate456_chunkChecks2 :
    compactCertificate456.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate456.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate456_chunkChecks2_0
    compactCertificate456_chunkChecks2_1 compactCertificate456_chunkChecks2_2

theorem compactCertificate456_chunkChecks3_0 :
    compactCertificate456.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (655 / 2) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44086523782 / 1000000000000) (44086523926 / 1000000000000), orderedInterval (435998435 / 1000000000000) (435998580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (192988014175031 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6010161089 / 1000000000000) (-6010161088 / 1000000000000), orderedInterval (-51006027881 / 1000000000000) (-51006027880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (62408358595223 / 160000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38701613688 / 1000000000000) (38701613692 / 1000000000000), orderedInterval (11540201181 / 1000000000000) (11540201185 / 1000000000000)))) (orderedInterval (-1063808137 / 1000000000000) (-1063808044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (56313421217317 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83928005095 / 1000000000000) (83928016033 / 1000000000000), orderedInterval (-45316507853 / 1000000000000) (-45316496915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (151265770527649 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56875053496 / 1000000000000) (56875053499 / 1000000000000), orderedInterval (11343578317 / 1000000000000) (11343578321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (410715992365533 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30387371394 / 1000000000000) (-30387262883 / 1000000000000), orderedInterval (17823639891 / 1000000000000) (17823748402 / 1000000000000)))) (orderedInterval (4814741435 / 1000000000000) (4814771303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (302531541055429 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37986487413 / 1000000000000) (37986505657 / 1000000000000), orderedInterval (-15557393827 / 1000000000000) (-15557375583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (518392952083417 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31322022338 / 1000000000000) (31322024342 / 1000000000000), orderedInterval (-1199685516 / 1000000000000) (-1199683512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (381845902232203 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19721062313 / 1000000000000) (19721062314 / 1000000000000), orderedInterval (30717805411 / 1000000000000) (30717805412 / 1000000000000)))) (orderedInterval (-2593280708 / 1000000000000) (-2593280124 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate456_chunkChecks3_1 :
    compactCertificate456.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (585849810104869 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26361766688 / 1000000000000) (-26361766684 / 1000000000000), orderedInterval (-13187508701 / 1000000000000) (-13187508697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (338240545568701 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19590520753 / 1000000000000) (19590521854 / 1000000000000), orderedInterval (-33518432956 / 1000000000000) (-33518431855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (600213783666209 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6124071971 / 1000000000000) (-6124071970 / 1000000000000), orderedInterval (-28474330621 / 1000000000000) (-28474330620 / 1000000000000)))) (orderedInterval (27876628129 / 1000000000000) (27876629578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (560797574385221 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28163722793 / 1000000000000) (-28163722780 / 1000000000000), orderedInterval (-10702221198 / 1000000000000) (-10702221185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (400211610692693 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35651974864 / 1000000000000) (-35651974523 / 1000000000000), orderedInterval (-1190086927 / 1000000000000) (-1190086585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (453797311582947 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18817732819 / 1000000000000) (18817733845 / 1000000000000), orderedInterval (-27732847581 / 1000000000000) (-27732846555 / 1000000000000)))) (orderedInterval (-2240606849 / 1000000000000) (-2240606526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (378328887649843 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23191508516 / 1000000000000) (23191513199 / 1000000000000), orderedInterval (-28455599183 / 1000000000000) (-28455594500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (334265045802703 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27578475267 / 1000000000000) (-27578475266 / 1000000000000), orderedInterval (-27590473751 / 1000000000000) (-27590473750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (96883038879597 / 160000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (752102036 / 1000000000000) (752102037 / 1000000000000), orderedInterval (-32416618432 / 1000000000000) (-32416618431 / 1000000000000)))) (orderedInterval (2966198405 / 1000000000000) (2966198673 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate456_chunkChecks3_2 :
    compactCertificate456.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (267983584215959 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16408981415 / 1000000000000) (16408981739 / 1000000000000), orderedInterval (-40412866934 / 1000000000000) (-40412866610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (227172652176799 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42906231262 / 1000000000000) (42906249749 / 1000000000000), orderedInterval (-20099069060 / 1000000000000) (-20099050573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (142154097767797 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33473399796 / 1000000000000) (33473408366 / 1000000000000), orderedInterval (-49715144191 / 1000000000000) (-49715135621 / 1000000000000)))) (orderedInterval (-7410534073 / 1000000000000) (-7410533217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (76450946562699 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70454430510 / 1000000000000) (70454448625 / 1000000000000), orderedInterval (-41573726864 / 1000000000000) (-41573708748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (207579191745097 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23454815315 / 1000000000000) (23454817205 / 1000000000000), orderedInterval (-43672888469 / 1000000000000) (-43672886579 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (283431639836969 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3160410666 / 1000000000000) (-3160410665 / 1000000000000), orderedInterval (-42267336173 / 1000000000000) (-42267336172 / 1000000000000)))) (orderedInterval (-4613289803 / 1000000000000) (-4613289736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (119845902232203 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13238733414 / 1000000000000) (-13238733315 / 1000000000000), orderedInterval (63874793732 / 1000000000000) (63874793831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (487166938928363 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8776560345 / 1000000000000) (8776560346 / 1000000000000), orderedInterval (31111853792 / 1000000000000) (31111853793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (325404937908517 / 800000000000) 3 (IntervalRat.scale (655 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30130144423 / 1000000000000) (-30130106363 / 1000000000000), orderedInterval (25674671518 / 1000000000000) (25674709577 / 1000000000000)))) (orderedInterval (25492569489 / 1000000000000) (25492583494 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate456_chunkChecks3 :
    compactCertificate456.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate456.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate456_chunkChecks3_0
    compactCertificate456_chunkChecks3_1 compactCertificate456_chunkChecks3_2

theorem compactCertificate456_chunkChecks4_0 :
    compactCertificate456.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (655 / 2) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44086523782 / 1000000000000) (44086523926 / 1000000000000), orderedInterval (435998435 / 1000000000000) (435998580 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (192988014175031 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6010161089 / 1000000000000) (-6010161088 / 1000000000000), orderedInterval (-51006027881 / 1000000000000) (-51006027880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (62408358595223 / 160000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38701613688 / 1000000000000) (38701613692 / 1000000000000), orderedInterval (11540201181 / 1000000000000) (11540201185 / 1000000000000)))) (orderedInterval (22033722819 / 1000000000000) (22033722917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (56313421217317 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83928005095 / 1000000000000) (83928016033 / 1000000000000), orderedInterval (-45316507853 / 1000000000000) (-45316496915 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (151265770527649 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56875053496 / 1000000000000) (56875053499 / 1000000000000), orderedInterval (11343578317 / 1000000000000) (11343578321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (410715992365533 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30387371394 / 1000000000000) (-30387262883 / 1000000000000), orderedInterval (17823639891 / 1000000000000) (17823748402 / 1000000000000)))) (orderedInterval (13244785969 / 1000000000000) (13244832878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (302531541055429 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37986487413 / 1000000000000) (37986505657 / 1000000000000), orderedInterval (-15557393827 / 1000000000000) (-15557375583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (518392952083417 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31322022338 / 1000000000000) (31322024342 / 1000000000000), orderedInterval (-1199685516 / 1000000000000) (-1199683512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (381845902232203 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19721062313 / 1000000000000) (19721062314 / 1000000000000), orderedInterval (30717805411 / 1000000000000) (30717805412 / 1000000000000)))) (orderedInterval (-12640215801 / 1000000000000) (-12640214659 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate456_chunkChecks4_1 :
    compactCertificate456.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (585849810104869 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26361766688 / 1000000000000) (-26361766684 / 1000000000000), orderedInterval (-13187508701 / 1000000000000) (-13187508697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (338240545568701 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19590520753 / 1000000000000) (19590521854 / 1000000000000), orderedInterval (-33518432956 / 1000000000000) (-33518431855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (600213783666209 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6124071971 / 1000000000000) (-6124071970 / 1000000000000), orderedInterval (-28474330621 / 1000000000000) (-28474330620 / 1000000000000)))) (orderedInterval (96987086160 / 1000000000000) (96987089215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (560797574385221 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-28163722793 / 1000000000000) (-28163722780 / 1000000000000), orderedInterval (-10702221198 / 1000000000000) (-10702221185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (400211610692693 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35651974864 / 1000000000000) (-35651974523 / 1000000000000), orderedInterval (-1190086927 / 1000000000000) (-1190086585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (453797311582947 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18817732819 / 1000000000000) (18817733845 / 1000000000000), orderedInterval (-27732847581 / 1000000000000) (-27732846555 / 1000000000000)))) (orderedInterval (-8526094145 / 1000000000000) (-8526093608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (378328887649843 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23191508516 / 1000000000000) (23191513199 / 1000000000000), orderedInterval (-28455599183 / 1000000000000) (-28455594500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (334265045802703 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27578475267 / 1000000000000) (-27578475266 / 1000000000000), orderedInterval (-27590473751 / 1000000000000) (-27590473750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (96883038879597 / 160000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (752102036 / 1000000000000) (752102037 / 1000000000000), orderedInterval (-32416618432 / 1000000000000) (-32416618431 / 1000000000000)))) (orderedInterval (5552730108 / 1000000000000) (5552730509 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate456_chunkChecks4_2 :
    compactCertificate456.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (267983584215959 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (16408981415 / 1000000000000) (16408981739 / 1000000000000), orderedInterval (-40412866934 / 1000000000000) (-40412866610 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (227172652176799 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42906231262 / 1000000000000) (42906249749 / 1000000000000), orderedInterval (-20099069060 / 1000000000000) (-20099050573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (142154097767797 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33473399796 / 1000000000000) (33473408366 / 1000000000000), orderedInterval (-49715144191 / 1000000000000) (-49715135621 / 1000000000000)))) (orderedInterval (-4104590525 / 1000000000000) (-4104589778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (76450946562699 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70454430510 / 1000000000000) (70454448625 / 1000000000000), orderedInterval (-41573726864 / 1000000000000) (-41573708748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (207579191745097 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23454815315 / 1000000000000) (23454817205 / 1000000000000), orderedInterval (-43672888469 / 1000000000000) (-43672886579 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (283431639836969 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3160410666 / 1000000000000) (-3160410665 / 1000000000000), orderedInterval (-42267336173 / 1000000000000) (-42267336172 / 1000000000000)))) (orderedInterval (140799177 / 1000000000000) (140799234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (119845902232203 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13238733414 / 1000000000000) (-13238733315 / 1000000000000), orderedInterval (63874793732 / 1000000000000) (63874793831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (487166938928363 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8776560345 / 1000000000000) (8776560346 / 1000000000000), orderedInterval (31111853792 / 1000000000000) (31111853793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (325404937908517 / 800000000000) 4 (IntervalRat.scale (655 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30130144423 / 1000000000000) (-30130106363 / 1000000000000), orderedInterval (25674671518 / 1000000000000) (25674709577 / 1000000000000)))) (orderedInterval (4752624507 / 1000000000000) (4752642049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate456_chunkChecks4 :
    compactCertificate456.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate456.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate456_chunkChecks4_0
    compactCertificate456_chunkChecks4_1 compactCertificate456_chunkChecks4_2

theorem compactCertificate456_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate456.chunkCheck r b = true :=
  compactCertificate456.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate456_chunkChecks0
    · exact compactCertificate456_chunkChecks1
    · exact compactCertificate456_chunkChecks2
    · exact compactCertificate456_chunkChecks3
    · exact compactCertificate456_chunkChecks4)

theorem compactCertificate456_coefficient0 :
    compactCertificate456.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate456_coefficient1 :
    compactCertificate456.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate456_coefficient2 :
    compactCertificate456.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate456_coefficient3 :
    compactCertificate456.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate456_coefficient4 :
    compactCertificate456.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate456_coefficients : ∀ r : Fin 5,
    compactCertificate456.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate456_coefficient0
  · exact compactCertificate456_coefficient1
  · exact compactCertificate456_coefficient2
  · exact compactCertificate456_coefficient3
  · exact compactCertificate456_coefficient4

theorem compactCertificate456_lower : (1 : ℚ) ≤ compactCertificate456.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate456, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate456_proves {t : ℝ} (ht : t ∈ compactCertificate456.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate456.proves compactCertificate456_states compactCertificate456_chunks
    compactCertificate456_coefficients compactCertificate456_lower ht

end Erdos232
