/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate361 : CompactCertificate where
  left := 232
  right := 233
  center := 465 / 2
  grid := fun i =>
    match i.val with
    | 0 => 74
    | 1 => 55
    | 2 => 88
    | 3 => 16
    | 4 => 43
    | 5 => 116
    | 6 => 85
    | 7 => 147
    | 8 => 108
    | 9 => 166
    | 10 => 96
    | 11 => 170
    | 12 => 158
    | 13 => 113
    | 14 => 128
    | 15 => 107
    | 16 => 94
    | 17 => 137
    | 18 => 76
    | 19 => 64
    | 20 => 40
    | 21 => 22
    | 22 => 59
    | 23 => 80
    | 24 => 34
    | 25 => 138
    | _ => 92
  point := fun i =>
    match i.val with
    | 0 => 465 / 2
    | 1 => 137006758154793 / 800000000000
    | 2 => 44305170605769 / 160000000000
    | 3 => 39978230329851 / 800000000000
    | 4 => 107387150069247 / 800000000000
    | 5 => 291577002213699 / 800000000000
    | 6 => 214774300138587 / 800000000000
    | 7 => 368019423998151 / 800000000000
    | 8 => 271081442042709 / 800000000000
    | 9 => 415908643814907 / 800000000000
    | 10 => 240124967464803 / 800000000000
    | 11 => 426105968556927 / 800000000000
    | 12 => 398123468838363 / 800000000000
    | 13 => 284119693087179 / 800000000000
    | 14 => 322161450207741 / 800000000000
    | 15 => 268584630163629 / 800000000000
    | 16 => 237302666104209 / 800000000000
    | 17 => 68779561952691 / 160000000000
    | 18 => 190247888031177 / 800000000000
    | 19 => 161275241621697 / 800000000000
    | 20 => 100918557957291 / 800000000000
    | 21 => 54274336109397 / 800000000000
    | 22 => 147365380399191 / 800000000000
    | 23 => 201214828281207 / 800000000000
    | 24 => 85081442042709 / 800000000000
    | 25 => 345851338323189 / 800000000000
    | _ => 231012665843451 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (37791712588 / 1000000000000) (37791712589 / 1000000000000), orderedInterval (36111762353 / 1000000000000) (36111762354 / 1000000000000))
    | 1 => (orderedInterval (41312318078 / 1000000000000) (41312355365 / 1000000000000), orderedInterval (-44960305396 / 1000000000000) (-44960268109 / 1000000000000))
    | 2 => (orderedInterval (45224367566 / 1000000000000) (45224367567 / 1000000000000), orderedInterval (15849104376 / 1000000000000) (15849104377 / 1000000000000))
    | 3 => (orderedInterval (53137765553 / 1000000000000) (53137765554 / 1000000000000), orderedInterval (99047808495 / 1000000000000) (99047808496 / 1000000000000))
    | 4 => (orderedInterval (4822176239 / 1000000000000) (4822176254 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
    | 5 => (orderedInterval (30884664616 / 1000000000000) (30884664617 / 1000000000000), orderedInterval (28114892890 / 1000000000000) (28114892891 / 1000000000000))
    | 6 => (orderedInterval (-38865093581 / 1000000000000) (-38864982458 / 1000000000000), orderedInterval (29411967811 / 1000000000000) (29412078934 / 1000000000000))
    | 7 => (orderedInterval (31397539597 / 1000000000000) (31397640027 / 1000000000000), orderedInterval (-19985964369 / 1000000000000) (-19985863940 / 1000000000000))
    | 8 => (orderedInterval (14651868319 / 1000000000000) (14651868320 / 1000000000000), orderedInterval (40771517857 / 1000000000000) (40771517858 / 1000000000000))
    | 9 => (orderedInterval (-25903295311 / 1000000000000) (-25903278767 / 1000000000000), orderedInterval (23552703828 / 1000000000000) (23552720371 / 1000000000000))
    | 10 => (orderedInterval (-27933599423 / 1000000000000) (-27933591158 / 1000000000000), orderedInterval (36661777648 / 1000000000000) (36661785913 / 1000000000000))
    | 11 => (orderedInterval (-21008542915 / 1000000000000) (-21008540508 / 1000000000000), orderedInterval (27476487715 / 1000000000000) (27476490121 / 1000000000000))
    | 12 => (orderedInterval (31438477264 / 1000000000000) (31438561156 / 1000000000000), orderedInterval (-17086244868 / 1000000000000) (-17086160975 / 1000000000000))
    | 13 => (orderedInterval (-34057688970 / 1000000000000) (-34057688969 / 1000000000000), orderedInterval (-25103850052 / 1000000000000) (-25103850051 / 1000000000000))
    | 14 => (orderedInterval (38905169342 / 1000000000000) (38905169356 / 1000000000000), orderedInterval (8152796506 / 1000000000000) (8152796520 / 1000000000000))
    | 15 => (orderedInterval (-15559823484 / 1000000000000) (-15559823483 / 1000000000000), orderedInterval (-40647633052 / 1000000000000) (-40647633051 / 1000000000000))
    | 16 => (orderedInterval (39905353144 / 1000000000000) (39905400512 / 1000000000000), orderedInterval (-23599096534 / 1000000000000) (-23599049167 / 1000000000000))
    | 17 => (orderedInterval (-9862614015 / 1000000000000) (-9862614014 / 1000000000000), orderedInterval (-37186387956 / 1000000000000) (-37186387955 / 1000000000000))
    | 18 => (orderedInterval (-8565186068 / 1000000000000) (-8565186039 / 1000000000000), orderedInterval (51044029761 / 1000000000000) (51044029791 / 1000000000000))
    | 19 => (orderedInterval (54393812978 / 1000000000000) (54393812980 / 1000000000000), orderedInterval (13980117806 / 1000000000000) (13980117808 / 1000000000000))
    | 20 => (orderedInterval (67826341764 / 1000000000000) (67826341765 / 1000000000000), orderedInterval (20853595851 / 1000000000000) (20853595852 / 1000000000000))
    | 21 => (orderedInterval (-45465833194 / 1000000000000) (-45465828089 / 1000000000000), orderedInterval (85872962376 / 1000000000000) (85872967481 / 1000000000000))
    | 22 => (orderedInterval (20848057645 / 1000000000000) (20848058277 / 1000000000000), orderedInterval (-55023626238 / 1000000000000) (-55023625607 / 1000000000000))
    | 23 => (orderedInterval (41670607617 / 1000000000000) (41670607618 / 1000000000000), orderedInterval (28106937041 / 1000000000000) (28106937042 / 1000000000000))
    | 24 => (orderedInterval (24475276408 / 1000000000000) (24475276409 / 1000000000000), orderedInterval (73281078234 / 1000000000000) (73281078235 / 1000000000000))
    | 25 => (orderedInterval (-16362623906 / 1000000000000) (-16362623558 / 1000000000000), orderedInterval (34729889534 / 1000000000000) (34729889881 / 1000000000000))
    | _ => (orderedInterval (23504117881 / 1000000000000) (23504117882 / 1000000000000), orderedInterval (40606332129 / 1000000000000) (40606332130 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (18018079990 / 1000000000000) (18018080355 / 1000000000000)
      | 1 => orderedInterval (-2596020742 / 1000000000000) (-2596020713 / 1000000000000)
      | 2 => orderedInterval (-614322098 / 1000000000000) (-614318987 / 1000000000000)
      | 3 => orderedInterval (-453438175 / 1000000000000) (-453434188 / 1000000000000)
      | 4 => orderedInterval (-3985038307 / 1000000000000) (-3985036764 / 1000000000000)
      | 5 => orderedInterval (-2715855060 / 1000000000000) (-2715852326 / 1000000000000)
      | 6 => orderedInterval (498925998 / 1000000000000) (498926062 / 1000000000000)
      | 7 => orderedInterval (-2827033480 / 1000000000000) (-2827033343 / 1000000000000)
      | _ => orderedInterval (-2930504413 / 1000000000000) (-2930504319 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15112528124 / 1000000000000) (15112528399 / 1000000000000)
      | 1 => orderedInterval (-4812668004 / 1000000000000) (-4812667971 / 1000000000000)
      | 2 => orderedInterval (2655796305 / 1000000000000) (2655802458 / 1000000000000)
      | 3 => orderedInterval (3096852526 / 1000000000000) (3096860865 / 1000000000000)
      | 4 => orderedInterval (-3037402249 / 1000000000000) (-3037398961 / 1000000000000)
      | 5 => orderedInterval (-715188478 / 1000000000000) (-715184986 / 1000000000000)
      | 6 => orderedInterval (-8665690265 / 1000000000000) (-8665690206 / 1000000000000)
      | 7 => orderedInterval (-1803955825 / 1000000000000) (-1803955760 / 1000000000000)
      | _ => orderedInterval (-14517241426 / 1000000000000) (-14517241282 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19017560637 / 1000000000000) (-19017560425 / 1000000000000)
      | 1 => orderedInterval (5384121410 / 1000000000000) (5384121455 / 1000000000000)
      | 2 => orderedInterval (3027666833 / 1000000000000) (3027679028 / 1000000000000)
      | 3 => orderedInterval (-3903770571 / 1000000000000) (-3903752611 / 1000000000000)
      | 4 => orderedInterval (10718723011 / 1000000000000) (10718730039 / 1000000000000)
      | 5 => orderedInterval (4958116169 / 1000000000000) (4958120645 / 1000000000000)
      | 6 => orderedInterval (269056777 / 1000000000000) (269056834 / 1000000000000)
      | 7 => orderedInterval (3970602272 / 1000000000000) (3970602315 / 1000000000000)
      | _ => orderedInterval (2229199232 / 1000000000000) (2229199464 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15635152227 / 1000000000000) (-15635152062 / 1000000000000)
      | 1 => orderedInterval (8169789559 / 1000000000000) (8169789626 / 1000000000000)
      | 2 => orderedInterval (-7838340104 / 1000000000000) (-7838315984 / 1000000000000)
      | 3 => orderedInterval (-5999011720 / 1000000000000) (-5998972453 / 1000000000000)
      | 4 => orderedInterval (5604399397 / 1000000000000) (5604414406 / 1000000000000)
      | 5 => orderedInterval (4605249070 / 1000000000000) (4605254793 / 1000000000000)
      | 6 => orderedInterval (9139663242 / 1000000000000) (9139663298 / 1000000000000)
      | 7 => orderedInterval (2128573706 / 1000000000000) (2128573742 / 1000000000000)
      | _ => orderedInterval (32719306767 / 1000000000000) (32719307156 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (20566479617 / 1000000000000) (20566479750 / 1000000000000)
      | 1 => orderedInterval (-13310837068 / 1000000000000) (-13310836966 / 1000000000000)
      | 2 => orderedInterval (-13177089442 / 1000000000000) (-13177041625 / 1000000000000)
      | 3 => orderedInterval (27111745675 / 1000000000000) (27111832613 / 1000000000000)
      | 4 => orderedInterval (-31267630326 / 1000000000000) (-31267598188 / 1000000000000)
      | 5 => orderedInterval (-9822178223 / 1000000000000) (-9822170875 / 1000000000000)
      | 6 => orderedInterval (-128428546 / 1000000000000) (-128428491 / 1000000000000)
      | 7 => orderedInterval (-4572399933 / 1000000000000) (-4572399899 / 1000000000000)
      | _ => orderedInterval (5153149354 / 1000000000000) (5153150026 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2394793713 / 1000000000000) (2394805777 / 1000000000000)
    | 1 => orderedInterval (-12686969292 / 1000000000000) (-12686947444 / 1000000000000)
    | 2 => orderedInterval (7636154496 / 1000000000000) (7636196744 / 1000000000000)
    | 3 => orderedInterval (32894477690 / 1000000000000) (32894562522 / 1000000000000)
    | _ => orderedInterval (-19447188892 / 1000000000000) (-19447013655 / 1000000000000)

theorem compactCertificate361_stateChecks0 :
    compactCertificate361.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (465 / 2)) (orderedInterval (37791712588 / 1000000000000) (37791712589 / 1000000000000), orderedInterval (36111762353 / 1000000000000) (36111762354 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (137006758154793 / 800000000000)) (orderedInterval (41312318078 / 1000000000000) (41312355365 / 1000000000000), orderedInterval (-44960305396 / 1000000000000) (-44960268109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (44305170605769 / 160000000000)) (orderedInterval (45224367566 / 1000000000000) (45224367567 / 1000000000000), orderedInterval (15849104376 / 1000000000000) (15849104377 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks1 :
    compactCertificate361.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (39978230329851 / 800000000000)) (orderedInterval (53137765553 / 1000000000000) (53137765554 / 1000000000000), orderedInterval (99047808495 / 1000000000000) (99047808496 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (107387150069247 / 800000000000)) (orderedInterval (4822176239 / 1000000000000) (4822176254 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (291577002213699 / 800000000000)) (orderedInterval (30884664616 / 1000000000000) (30884664617 / 1000000000000), orderedInterval (28114892890 / 1000000000000) (28114892891 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks2 :
    compactCertificate361.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (214774300138587 / 800000000000)) (orderedInterval (-38865093581 / 1000000000000) (-38864982458 / 1000000000000), orderedInterval (29411967811 / 1000000000000) (29412078934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (368019423998151 / 800000000000)) (orderedInterval (31397539597 / 1000000000000) (31397640027 / 1000000000000), orderedInterval (-19985964369 / 1000000000000) (-19985863940 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (271081442042709 / 800000000000)) (orderedInterval (14651868319 / 1000000000000) (14651868320 / 1000000000000), orderedInterval (40771517857 / 1000000000000) (40771517858 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks3 :
    compactCertificate361.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (415908643814907 / 800000000000)) (orderedInterval (-25903295311 / 1000000000000) (-25903278767 / 1000000000000), orderedInterval (23552703828 / 1000000000000) (23552720371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (240124967464803 / 800000000000)) (orderedInterval (-27933599423 / 1000000000000) (-27933591158 / 1000000000000), orderedInterval (36661777648 / 1000000000000) (36661785913 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (426105968556927 / 800000000000)) (orderedInterval (-21008542915 / 1000000000000) (-21008540508 / 1000000000000), orderedInterval (27476487715 / 1000000000000) (27476490121 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks4 :
    compactCertificate361.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (398123468838363 / 800000000000)) (orderedInterval (31438477264 / 1000000000000) (31438561156 / 1000000000000), orderedInterval (-17086244868 / 1000000000000) (-17086160975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (284119693087179 / 800000000000)) (orderedInterval (-34057688970 / 1000000000000) (-34057688969 / 1000000000000), orderedInterval (-25103850052 / 1000000000000) (-25103850051 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (322161450207741 / 800000000000)) (orderedInterval (38905169342 / 1000000000000) (38905169356 / 1000000000000), orderedInterval (8152796506 / 1000000000000) (8152796520 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks5 :
    compactCertificate361.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (268584630163629 / 800000000000)) (orderedInterval (-15559823484 / 1000000000000) (-15559823483 / 1000000000000), orderedInterval (-40647633052 / 1000000000000) (-40647633051 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (237302666104209 / 800000000000)) (orderedInterval (39905353144 / 1000000000000) (39905400512 / 1000000000000), orderedInterval (-23599096534 / 1000000000000) (-23599049167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (68779561952691 / 160000000000)) (orderedInterval (-9862614015 / 1000000000000) (-9862614014 / 1000000000000), orderedInterval (-37186387956 / 1000000000000) (-37186387955 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks6 :
    compactCertificate361.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (190247888031177 / 800000000000)) (orderedInterval (-8565186068 / 1000000000000) (-8565186039 / 1000000000000), orderedInterval (51044029761 / 1000000000000) (51044029791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (161275241621697 / 800000000000)) (orderedInterval (54393812978 / 1000000000000) (54393812980 / 1000000000000), orderedInterval (13980117806 / 1000000000000) (13980117808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (100918557957291 / 800000000000)) (orderedInterval (67826341764 / 1000000000000) (67826341765 / 1000000000000), orderedInterval (20853595851 / 1000000000000) (20853595852 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks7 :
    compactCertificate361.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (54274336109397 / 800000000000)) (orderedInterval (-45465833194 / 1000000000000) (-45465828089 / 1000000000000), orderedInterval (85872962376 / 1000000000000) (85872967481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (147365380399191 / 800000000000)) (orderedInterval (20848057645 / 1000000000000) (20848058277 / 1000000000000), orderedInterval (-55023626238 / 1000000000000) (-55023625607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201214828281207 / 800000000000)) (orderedInterval (41670607617 / 1000000000000) (41670607618 / 1000000000000), orderedInterval (28106937041 / 1000000000000) (28106937042 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_stateChecks8 :
    compactCertificate361.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (85081442042709 / 800000000000)) (orderedInterval (24475276408 / 1000000000000) (24475276409 / 1000000000000), orderedInterval (73281078234 / 1000000000000) (73281078235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (345851338323189 / 800000000000)) (orderedInterval (-16362623906 / 1000000000000) (-16362623558 / 1000000000000), orderedInterval (34729889534 / 1000000000000) (34729889881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (231012665843451 / 800000000000)) (orderedInterval (23504117881 / 1000000000000) (23504117882 / 1000000000000), orderedInterval (40606332129 / 1000000000000) (40606332130 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_states : ∀ j,
    BesselStateValid (compactCertificate361.point j) (compactCertificate361.state j) :=
  compactCertificate361.statesValid_of_checks3 compactCertificate361_stateChecks0
    compactCertificate361_stateChecks1 compactCertificate361_stateChecks2
    compactCertificate361_stateChecks3 compactCertificate361_stateChecks4
    compactCertificate361_stateChecks5 compactCertificate361_stateChecks6
    compactCertificate361_stateChecks7 compactCertificate361_stateChecks8

theorem compactCertificate361_chunkChecks0_0 :
    compactCertificate361.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (465 / 2) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791712588 / 1000000000000) (37791712589 / 1000000000000), orderedInterval (36111762353 / 1000000000000) (36111762354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (137006758154793 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41312318078 / 1000000000000) (41312355365 / 1000000000000), orderedInterval (-44960305396 / 1000000000000) (-44960268109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (44305170605769 / 160000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45224367566 / 1000000000000) (45224367567 / 1000000000000), orderedInterval (15849104376 / 1000000000000) (15849104377 / 1000000000000)))) (orderedInterval (18018079990 / 1000000000000) (18018080355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (39978230329851 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53137765553 / 1000000000000) (53137765554 / 1000000000000), orderedInterval (99047808495 / 1000000000000) (99047808496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (107387150069247 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4822176239 / 1000000000000) (4822176254 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (291577002213699 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30884664616 / 1000000000000) (30884664617 / 1000000000000), orderedInterval (28114892890 / 1000000000000) (28114892891 / 1000000000000)))) (orderedInterval (-2596020742 / 1000000000000) (-2596020713 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (214774300138587 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38865093581 / 1000000000000) (-38864982458 / 1000000000000), orderedInterval (29411967811 / 1000000000000) (29412078934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (368019423998151 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31397539597 / 1000000000000) (31397640027 / 1000000000000), orderedInterval (-19985964369 / 1000000000000) (-19985863940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (271081442042709 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14651868319 / 1000000000000) (14651868320 / 1000000000000), orderedInterval (40771517857 / 1000000000000) (40771517858 / 1000000000000)))) (orderedInterval (-614322098 / 1000000000000) (-614318987 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks0_1 :
    compactCertificate361.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (415908643814907 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25903295311 / 1000000000000) (-25903278767 / 1000000000000), orderedInterval (23552703828 / 1000000000000) (23552720371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (240124967464803 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27933599423 / 1000000000000) (-27933591158 / 1000000000000), orderedInterval (36661777648 / 1000000000000) (36661785913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (426105968556927 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21008542915 / 1000000000000) (-21008540508 / 1000000000000), orderedInterval (27476487715 / 1000000000000) (27476490121 / 1000000000000)))) (orderedInterval (-453438175 / 1000000000000) (-453434188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (398123468838363 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31438477264 / 1000000000000) (31438561156 / 1000000000000), orderedInterval (-17086244868 / 1000000000000) (-17086160975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (284119693087179 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34057688970 / 1000000000000) (-34057688969 / 1000000000000), orderedInterval (-25103850052 / 1000000000000) (-25103850051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (322161450207741 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38905169342 / 1000000000000) (38905169356 / 1000000000000), orderedInterval (8152796506 / 1000000000000) (8152796520 / 1000000000000)))) (orderedInterval (-3985038307 / 1000000000000) (-3985036764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (268584630163629 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15559823484 / 1000000000000) (-15559823483 / 1000000000000), orderedInterval (-40647633052 / 1000000000000) (-40647633051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (237302666104209 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39905353144 / 1000000000000) (39905400512 / 1000000000000), orderedInterval (-23599096534 / 1000000000000) (-23599049167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (68779561952691 / 160000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9862614015 / 1000000000000) (-9862614014 / 1000000000000), orderedInterval (-37186387956 / 1000000000000) (-37186387955 / 1000000000000)))) (orderedInterval (-2715855060 / 1000000000000) (-2715852326 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks0_2 :
    compactCertificate361.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (190247888031177 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8565186068 / 1000000000000) (-8565186039 / 1000000000000), orderedInterval (51044029761 / 1000000000000) (51044029791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (161275241621697 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54393812978 / 1000000000000) (54393812980 / 1000000000000), orderedInterval (13980117806 / 1000000000000) (13980117808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (100918557957291 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67826341764 / 1000000000000) (67826341765 / 1000000000000), orderedInterval (20853595851 / 1000000000000) (20853595852 / 1000000000000)))) (orderedInterval (498925998 / 1000000000000) (498926062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (54274336109397 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45465833194 / 1000000000000) (-45465828089 / 1000000000000), orderedInterval (85872962376 / 1000000000000) (85872967481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (147365380399191 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20848057645 / 1000000000000) (20848058277 / 1000000000000), orderedInterval (-55023626238 / 1000000000000) (-55023625607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (201214828281207 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41670607617 / 1000000000000) (41670607618 / 1000000000000), orderedInterval (28106937041 / 1000000000000) (28106937042 / 1000000000000)))) (orderedInterval (-2827033480 / 1000000000000) (-2827033343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (85081442042709 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (24475276408 / 1000000000000) (24475276409 / 1000000000000), orderedInterval (73281078234 / 1000000000000) (73281078235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (345851338323189 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16362623906 / 1000000000000) (-16362623558 / 1000000000000), orderedInterval (34729889534 / 1000000000000) (34729889881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (231012665843451 / 800000000000) 0 (IntervalRat.scale (465 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23504117881 / 1000000000000) (23504117882 / 1000000000000), orderedInterval (40606332129 / 1000000000000) (40606332130 / 1000000000000)))) (orderedInterval (-2930504413 / 1000000000000) (-2930504319 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks0 :
    compactCertificate361.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate361.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate361_chunkChecks0_0
    compactCertificate361_chunkChecks0_1 compactCertificate361_chunkChecks0_2

theorem compactCertificate361_chunkChecks1_0 :
    compactCertificate361.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (465 / 2) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791712588 / 1000000000000) (37791712589 / 1000000000000), orderedInterval (36111762353 / 1000000000000) (36111762354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (137006758154793 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41312318078 / 1000000000000) (41312355365 / 1000000000000), orderedInterval (-44960305396 / 1000000000000) (-44960268109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (44305170605769 / 160000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45224367566 / 1000000000000) (45224367567 / 1000000000000), orderedInterval (15849104376 / 1000000000000) (15849104377 / 1000000000000)))) (orderedInterval (15112528124 / 1000000000000) (15112528399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (39978230329851 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53137765553 / 1000000000000) (53137765554 / 1000000000000), orderedInterval (99047808495 / 1000000000000) (99047808496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (107387150069247 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4822176239 / 1000000000000) (4822176254 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (291577002213699 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30884664616 / 1000000000000) (30884664617 / 1000000000000), orderedInterval (28114892890 / 1000000000000) (28114892891 / 1000000000000)))) (orderedInterval (-4812668004 / 1000000000000) (-4812667971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (214774300138587 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38865093581 / 1000000000000) (-38864982458 / 1000000000000), orderedInterval (29411967811 / 1000000000000) (29412078934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (368019423998151 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31397539597 / 1000000000000) (31397640027 / 1000000000000), orderedInterval (-19985964369 / 1000000000000) (-19985863940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (271081442042709 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14651868319 / 1000000000000) (14651868320 / 1000000000000), orderedInterval (40771517857 / 1000000000000) (40771517858 / 1000000000000)))) (orderedInterval (2655796305 / 1000000000000) (2655802458 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks1_1 :
    compactCertificate361.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (415908643814907 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25903295311 / 1000000000000) (-25903278767 / 1000000000000), orderedInterval (23552703828 / 1000000000000) (23552720371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (240124967464803 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27933599423 / 1000000000000) (-27933591158 / 1000000000000), orderedInterval (36661777648 / 1000000000000) (36661785913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (426105968556927 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21008542915 / 1000000000000) (-21008540508 / 1000000000000), orderedInterval (27476487715 / 1000000000000) (27476490121 / 1000000000000)))) (orderedInterval (3096852526 / 1000000000000) (3096860865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (398123468838363 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31438477264 / 1000000000000) (31438561156 / 1000000000000), orderedInterval (-17086244868 / 1000000000000) (-17086160975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (284119693087179 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34057688970 / 1000000000000) (-34057688969 / 1000000000000), orderedInterval (-25103850052 / 1000000000000) (-25103850051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (322161450207741 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38905169342 / 1000000000000) (38905169356 / 1000000000000), orderedInterval (8152796506 / 1000000000000) (8152796520 / 1000000000000)))) (orderedInterval (-3037402249 / 1000000000000) (-3037398961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (268584630163629 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15559823484 / 1000000000000) (-15559823483 / 1000000000000), orderedInterval (-40647633052 / 1000000000000) (-40647633051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (237302666104209 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39905353144 / 1000000000000) (39905400512 / 1000000000000), orderedInterval (-23599096534 / 1000000000000) (-23599049167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (68779561952691 / 160000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9862614015 / 1000000000000) (-9862614014 / 1000000000000), orderedInterval (-37186387956 / 1000000000000) (-37186387955 / 1000000000000)))) (orderedInterval (-715188478 / 1000000000000) (-715184986 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks1_2 :
    compactCertificate361.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (190247888031177 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8565186068 / 1000000000000) (-8565186039 / 1000000000000), orderedInterval (51044029761 / 1000000000000) (51044029791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (161275241621697 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54393812978 / 1000000000000) (54393812980 / 1000000000000), orderedInterval (13980117806 / 1000000000000) (13980117808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (100918557957291 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67826341764 / 1000000000000) (67826341765 / 1000000000000), orderedInterval (20853595851 / 1000000000000) (20853595852 / 1000000000000)))) (orderedInterval (-8665690265 / 1000000000000) (-8665690206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (54274336109397 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45465833194 / 1000000000000) (-45465828089 / 1000000000000), orderedInterval (85872962376 / 1000000000000) (85872967481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (147365380399191 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20848057645 / 1000000000000) (20848058277 / 1000000000000), orderedInterval (-55023626238 / 1000000000000) (-55023625607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (201214828281207 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41670607617 / 1000000000000) (41670607618 / 1000000000000), orderedInterval (28106937041 / 1000000000000) (28106937042 / 1000000000000)))) (orderedInterval (-1803955825 / 1000000000000) (-1803955760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (85081442042709 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (24475276408 / 1000000000000) (24475276409 / 1000000000000), orderedInterval (73281078234 / 1000000000000) (73281078235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (345851338323189 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16362623906 / 1000000000000) (-16362623558 / 1000000000000), orderedInterval (34729889534 / 1000000000000) (34729889881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (231012665843451 / 800000000000) 1 (IntervalRat.scale (465 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23504117881 / 1000000000000) (23504117882 / 1000000000000), orderedInterval (40606332129 / 1000000000000) (40606332130 / 1000000000000)))) (orderedInterval (-14517241426 / 1000000000000) (-14517241282 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks1 :
    compactCertificate361.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate361.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate361_chunkChecks1_0
    compactCertificate361_chunkChecks1_1 compactCertificate361_chunkChecks1_2

theorem compactCertificate361_chunkChecks2_0 :
    compactCertificate361.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (465 / 2) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791712588 / 1000000000000) (37791712589 / 1000000000000), orderedInterval (36111762353 / 1000000000000) (36111762354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (137006758154793 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41312318078 / 1000000000000) (41312355365 / 1000000000000), orderedInterval (-44960305396 / 1000000000000) (-44960268109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (44305170605769 / 160000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45224367566 / 1000000000000) (45224367567 / 1000000000000), orderedInterval (15849104376 / 1000000000000) (15849104377 / 1000000000000)))) (orderedInterval (-19017560637 / 1000000000000) (-19017560425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (39978230329851 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53137765553 / 1000000000000) (53137765554 / 1000000000000), orderedInterval (99047808495 / 1000000000000) (99047808496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (107387150069247 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4822176239 / 1000000000000) (4822176254 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (291577002213699 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30884664616 / 1000000000000) (30884664617 / 1000000000000), orderedInterval (28114892890 / 1000000000000) (28114892891 / 1000000000000)))) (orderedInterval (5384121410 / 1000000000000) (5384121455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (214774300138587 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38865093581 / 1000000000000) (-38864982458 / 1000000000000), orderedInterval (29411967811 / 1000000000000) (29412078934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (368019423998151 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31397539597 / 1000000000000) (31397640027 / 1000000000000), orderedInterval (-19985964369 / 1000000000000) (-19985863940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (271081442042709 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14651868319 / 1000000000000) (14651868320 / 1000000000000), orderedInterval (40771517857 / 1000000000000) (40771517858 / 1000000000000)))) (orderedInterval (3027666833 / 1000000000000) (3027679028 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks2_1 :
    compactCertificate361.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (415908643814907 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25903295311 / 1000000000000) (-25903278767 / 1000000000000), orderedInterval (23552703828 / 1000000000000) (23552720371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (240124967464803 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27933599423 / 1000000000000) (-27933591158 / 1000000000000), orderedInterval (36661777648 / 1000000000000) (36661785913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (426105968556927 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21008542915 / 1000000000000) (-21008540508 / 1000000000000), orderedInterval (27476487715 / 1000000000000) (27476490121 / 1000000000000)))) (orderedInterval (-3903770571 / 1000000000000) (-3903752611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (398123468838363 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31438477264 / 1000000000000) (31438561156 / 1000000000000), orderedInterval (-17086244868 / 1000000000000) (-17086160975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (284119693087179 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34057688970 / 1000000000000) (-34057688969 / 1000000000000), orderedInterval (-25103850052 / 1000000000000) (-25103850051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (322161450207741 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38905169342 / 1000000000000) (38905169356 / 1000000000000), orderedInterval (8152796506 / 1000000000000) (8152796520 / 1000000000000)))) (orderedInterval (10718723011 / 1000000000000) (10718730039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (268584630163629 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15559823484 / 1000000000000) (-15559823483 / 1000000000000), orderedInterval (-40647633052 / 1000000000000) (-40647633051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (237302666104209 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39905353144 / 1000000000000) (39905400512 / 1000000000000), orderedInterval (-23599096534 / 1000000000000) (-23599049167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (68779561952691 / 160000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9862614015 / 1000000000000) (-9862614014 / 1000000000000), orderedInterval (-37186387956 / 1000000000000) (-37186387955 / 1000000000000)))) (orderedInterval (4958116169 / 1000000000000) (4958120645 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks2_2 :
    compactCertificate361.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (190247888031177 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8565186068 / 1000000000000) (-8565186039 / 1000000000000), orderedInterval (51044029761 / 1000000000000) (51044029791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (161275241621697 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54393812978 / 1000000000000) (54393812980 / 1000000000000), orderedInterval (13980117806 / 1000000000000) (13980117808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (100918557957291 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67826341764 / 1000000000000) (67826341765 / 1000000000000), orderedInterval (20853595851 / 1000000000000) (20853595852 / 1000000000000)))) (orderedInterval (269056777 / 1000000000000) (269056834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (54274336109397 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45465833194 / 1000000000000) (-45465828089 / 1000000000000), orderedInterval (85872962376 / 1000000000000) (85872967481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (147365380399191 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20848057645 / 1000000000000) (20848058277 / 1000000000000), orderedInterval (-55023626238 / 1000000000000) (-55023625607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (201214828281207 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41670607617 / 1000000000000) (41670607618 / 1000000000000), orderedInterval (28106937041 / 1000000000000) (28106937042 / 1000000000000)))) (orderedInterval (3970602272 / 1000000000000) (3970602315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (85081442042709 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (24475276408 / 1000000000000) (24475276409 / 1000000000000), orderedInterval (73281078234 / 1000000000000) (73281078235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (345851338323189 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16362623906 / 1000000000000) (-16362623558 / 1000000000000), orderedInterval (34729889534 / 1000000000000) (34729889881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (231012665843451 / 800000000000) 2 (IntervalRat.scale (465 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23504117881 / 1000000000000) (23504117882 / 1000000000000), orderedInterval (40606332129 / 1000000000000) (40606332130 / 1000000000000)))) (orderedInterval (2229199232 / 1000000000000) (2229199464 / 1000000000000))) = true
  rfl'

theorem compactCertificate361_chunkChecks2 :
    compactCertificate361.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate361.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate361_chunkChecks2_0
    compactCertificate361_chunkChecks2_1 compactCertificate361_chunkChecks2_2

theorem compactCertificate361_chunkChecks3_0 :
    compactCertificate361.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (465 / 2) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791712588 / 1000000000000) (37791712589 / 1000000000000), orderedInterval (36111762353 / 1000000000000) (36111762354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (137006758154793 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41312318078 / 1000000000000) (41312355365 / 1000000000000), orderedInterval (-44960305396 / 1000000000000) (-44960268109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (44305170605769 / 160000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45224367566 / 1000000000000) (45224367567 / 1000000000000), orderedInterval (15849104376 / 1000000000000) (15849104377 / 1000000000000)))) (orderedInterval (-15635152227 / 1000000000000) (-15635152062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (39978230329851 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53137765553 / 1000000000000) (53137765554 / 1000000000000), orderedInterval (99047808495 / 1000000000000) (99047808496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (107387150069247 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4822176239 / 1000000000000) (4822176254 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (291577002213699 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30884664616 / 1000000000000) (30884664617 / 1000000000000), orderedInterval (28114892890 / 1000000000000) (28114892891 / 1000000000000)))) (orderedInterval (8169789559 / 1000000000000) (8169789626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (214774300138587 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38865093581 / 1000000000000) (-38864982458 / 1000000000000), orderedInterval (29411967811 / 1000000000000) (29412078934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (368019423998151 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31397539597 / 1000000000000) (31397640027 / 1000000000000), orderedInterval (-19985964369 / 1000000000000) (-19985863940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (271081442042709 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14651868319 / 1000000000000) (14651868320 / 1000000000000), orderedInterval (40771517857 / 1000000000000) (40771517858 / 1000000000000)))) (orderedInterval (-7838340104 / 1000000000000) (-7838315984 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate361_chunkChecks3_1 :
    compactCertificate361.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (415908643814907 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25903295311 / 1000000000000) (-25903278767 / 1000000000000), orderedInterval (23552703828 / 1000000000000) (23552720371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (240124967464803 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27933599423 / 1000000000000) (-27933591158 / 1000000000000), orderedInterval (36661777648 / 1000000000000) (36661785913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (426105968556927 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21008542915 / 1000000000000) (-21008540508 / 1000000000000), orderedInterval (27476487715 / 1000000000000) (27476490121 / 1000000000000)))) (orderedInterval (-5999011720 / 1000000000000) (-5998972453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (398123468838363 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31438477264 / 1000000000000) (31438561156 / 1000000000000), orderedInterval (-17086244868 / 1000000000000) (-17086160975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (284119693087179 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34057688970 / 1000000000000) (-34057688969 / 1000000000000), orderedInterval (-25103850052 / 1000000000000) (-25103850051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (322161450207741 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38905169342 / 1000000000000) (38905169356 / 1000000000000), orderedInterval (8152796506 / 1000000000000) (8152796520 / 1000000000000)))) (orderedInterval (5604399397 / 1000000000000) (5604414406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (268584630163629 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15559823484 / 1000000000000) (-15559823483 / 1000000000000), orderedInterval (-40647633052 / 1000000000000) (-40647633051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (237302666104209 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39905353144 / 1000000000000) (39905400512 / 1000000000000), orderedInterval (-23599096534 / 1000000000000) (-23599049167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (68779561952691 / 160000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9862614015 / 1000000000000) (-9862614014 / 1000000000000), orderedInterval (-37186387956 / 1000000000000) (-37186387955 / 1000000000000)))) (orderedInterval (4605249070 / 1000000000000) (4605254793 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate361_chunkChecks3_2 :
    compactCertificate361.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (190247888031177 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8565186068 / 1000000000000) (-8565186039 / 1000000000000), orderedInterval (51044029761 / 1000000000000) (51044029791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (161275241621697 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54393812978 / 1000000000000) (54393812980 / 1000000000000), orderedInterval (13980117806 / 1000000000000) (13980117808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (100918557957291 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67826341764 / 1000000000000) (67826341765 / 1000000000000), orderedInterval (20853595851 / 1000000000000) (20853595852 / 1000000000000)))) (orderedInterval (9139663242 / 1000000000000) (9139663298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (54274336109397 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45465833194 / 1000000000000) (-45465828089 / 1000000000000), orderedInterval (85872962376 / 1000000000000) (85872967481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (147365380399191 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20848057645 / 1000000000000) (20848058277 / 1000000000000), orderedInterval (-55023626238 / 1000000000000) (-55023625607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (201214828281207 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41670607617 / 1000000000000) (41670607618 / 1000000000000), orderedInterval (28106937041 / 1000000000000) (28106937042 / 1000000000000)))) (orderedInterval (2128573706 / 1000000000000) (2128573742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (85081442042709 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (24475276408 / 1000000000000) (24475276409 / 1000000000000), orderedInterval (73281078234 / 1000000000000) (73281078235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (345851338323189 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16362623906 / 1000000000000) (-16362623558 / 1000000000000), orderedInterval (34729889534 / 1000000000000) (34729889881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (231012665843451 / 800000000000) 3 (IntervalRat.scale (465 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23504117881 / 1000000000000) (23504117882 / 1000000000000), orderedInterval (40606332129 / 1000000000000) (40606332130 / 1000000000000)))) (orderedInterval (32719306767 / 1000000000000) (32719307156 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate361_chunkChecks3 :
    compactCertificate361.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate361.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate361_chunkChecks3_0
    compactCertificate361_chunkChecks3_1 compactCertificate361_chunkChecks3_2

theorem compactCertificate361_chunkChecks4_0 :
    compactCertificate361.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (465 / 2) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37791712588 / 1000000000000) (37791712589 / 1000000000000), orderedInterval (36111762353 / 1000000000000) (36111762354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (137006758154793 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41312318078 / 1000000000000) (41312355365 / 1000000000000), orderedInterval (-44960305396 / 1000000000000) (-44960268109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (44305170605769 / 160000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (45224367566 / 1000000000000) (45224367567 / 1000000000000), orderedInterval (15849104376 / 1000000000000) (15849104377 / 1000000000000)))) (orderedInterval (20566479617 / 1000000000000) (20566479750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (39978230329851 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (53137765553 / 1000000000000) (53137765554 / 1000000000000), orderedInterval (99047808495 / 1000000000000) (99047808496 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (107387150069247 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (4822176239 / 1000000000000) (4822176254 / 1000000000000), orderedInterval (-68715802504 / 1000000000000) (-68715802489 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (291577002213699 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30884664616 / 1000000000000) (30884664617 / 1000000000000), orderedInterval (28114892890 / 1000000000000) (28114892891 / 1000000000000)))) (orderedInterval (-13310837068 / 1000000000000) (-13310836966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (214774300138587 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38865093581 / 1000000000000) (-38864982458 / 1000000000000), orderedInterval (29411967811 / 1000000000000) (29412078934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (368019423998151 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31397539597 / 1000000000000) (31397640027 / 1000000000000), orderedInterval (-19985964369 / 1000000000000) (-19985863940 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (271081442042709 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14651868319 / 1000000000000) (14651868320 / 1000000000000), orderedInterval (40771517857 / 1000000000000) (40771517858 / 1000000000000)))) (orderedInterval (-13177089442 / 1000000000000) (-13177041625 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate361_chunkChecks4_1 :
    compactCertificate361.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (415908643814907 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25903295311 / 1000000000000) (-25903278767 / 1000000000000), orderedInterval (23552703828 / 1000000000000) (23552720371 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (240124967464803 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27933599423 / 1000000000000) (-27933591158 / 1000000000000), orderedInterval (36661777648 / 1000000000000) (36661785913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (426105968556927 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21008542915 / 1000000000000) (-21008540508 / 1000000000000), orderedInterval (27476487715 / 1000000000000) (27476490121 / 1000000000000)))) (orderedInterval (27111745675 / 1000000000000) (27111832613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (398123468838363 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (31438477264 / 1000000000000) (31438561156 / 1000000000000), orderedInterval (-17086244868 / 1000000000000) (-17086160975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (284119693087179 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34057688970 / 1000000000000) (-34057688969 / 1000000000000), orderedInterval (-25103850052 / 1000000000000) (-25103850051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (322161450207741 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (38905169342 / 1000000000000) (38905169356 / 1000000000000), orderedInterval (8152796506 / 1000000000000) (8152796520 / 1000000000000)))) (orderedInterval (-31267630326 / 1000000000000) (-31267598188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (268584630163629 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15559823484 / 1000000000000) (-15559823483 / 1000000000000), orderedInterval (-40647633052 / 1000000000000) (-40647633051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (237302666104209 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (39905353144 / 1000000000000) (39905400512 / 1000000000000), orderedInterval (-23599096534 / 1000000000000) (-23599049167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (68779561952691 / 160000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9862614015 / 1000000000000) (-9862614014 / 1000000000000), orderedInterval (-37186387956 / 1000000000000) (-37186387955 / 1000000000000)))) (orderedInterval (-9822178223 / 1000000000000) (-9822170875 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate361_chunkChecks4_2 :
    compactCertificate361.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (190247888031177 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-8565186068 / 1000000000000) (-8565186039 / 1000000000000), orderedInterval (51044029761 / 1000000000000) (51044029791 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (161275241621697 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (54393812978 / 1000000000000) (54393812980 / 1000000000000), orderedInterval (13980117806 / 1000000000000) (13980117808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (100918557957291 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (67826341764 / 1000000000000) (67826341765 / 1000000000000), orderedInterval (20853595851 / 1000000000000) (20853595852 / 1000000000000)))) (orderedInterval (-128428546 / 1000000000000) (-128428491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (54274336109397 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45465833194 / 1000000000000) (-45465828089 / 1000000000000), orderedInterval (85872962376 / 1000000000000) (85872967481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (147365380399191 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20848057645 / 1000000000000) (20848058277 / 1000000000000), orderedInterval (-55023626238 / 1000000000000) (-55023625607 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (201214828281207 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41670607617 / 1000000000000) (41670607618 / 1000000000000), orderedInterval (28106937041 / 1000000000000) (28106937042 / 1000000000000)))) (orderedInterval (-4572399933 / 1000000000000) (-4572399899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (85081442042709 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (24475276408 / 1000000000000) (24475276409 / 1000000000000), orderedInterval (73281078234 / 1000000000000) (73281078235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (345851338323189 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-16362623906 / 1000000000000) (-16362623558 / 1000000000000), orderedInterval (34729889534 / 1000000000000) (34729889881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (231012665843451 / 800000000000) 4 (IntervalRat.scale (465 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23504117881 / 1000000000000) (23504117882 / 1000000000000), orderedInterval (40606332129 / 1000000000000) (40606332130 / 1000000000000)))) (orderedInterval (5153149354 / 1000000000000) (5153150026 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate361_chunkChecks4 :
    compactCertificate361.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate361.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate361_chunkChecks4_0
    compactCertificate361_chunkChecks4_1 compactCertificate361_chunkChecks4_2

theorem compactCertificate361_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate361.chunkCheck r b = true :=
  compactCertificate361.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate361_chunkChecks0
    · exact compactCertificate361_chunkChecks1
    · exact compactCertificate361_chunkChecks2
    · exact compactCertificate361_chunkChecks3
    · exact compactCertificate361_chunkChecks4)

theorem compactCertificate361_coefficient0 :
    compactCertificate361.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate361_coefficient1 :
    compactCertificate361.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate361_coefficient2 :
    compactCertificate361.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate361_coefficient3 :
    compactCertificate361.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate361_coefficient4 :
    compactCertificate361.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate361_coefficients : ∀ r : Fin 5,
    compactCertificate361.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate361_coefficient0
  · exact compactCertificate361_coefficient1
  · exact compactCertificate361_coefficient2
  · exact compactCertificate361_coefficient3
  · exact compactCertificate361_coefficient4

theorem compactCertificate361_lower : (1 : ℚ) ≤ compactCertificate361.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate361, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate361_proves {t : ℝ} (ht : t ∈ compactCertificate361.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate361.proves compactCertificate361_states compactCertificate361_chunks
    compactCertificate361_coefficients compactCertificate361_lower ht

end Erdos232
