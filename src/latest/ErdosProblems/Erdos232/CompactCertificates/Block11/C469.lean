/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate469 : CompactCertificate where
  left := 340
  right := 341
  center := 681 / 2
  grid := fun i =>
    match i.val with
    | 0 => 108
    | 1 => 80
    | 2 => 129
    | 3 => 23
    | 4 => 63
    | 5 => 170
    | 6 => 125
    | 7 => 215
    | 8 => 158
    | 9 => 242
    | 10 => 140
    | 11 => 248
    | 12 => 232
    | 13 => 166
    | 14 => 188
    | 15 => 157
    | 16 => 138
    | 17 => 200
    | 18 => 111
    | 19 => 94
    | 20 => 59
    | 21 => 32
    | 22 => 86
    | 23 => 117
    | 24 => 50
    | 25 => 202
    | _ => 135
  point := fun i =>
    match i.val with
    | 0 => 681 / 2
    | 1 => 1003243035520581 / 4000000000000
    | 2 => 324428184758373 / 800000000000
    | 3 => 292743815641167 / 4000000000000
    | 4 => 786351066636099 / 4000000000000
    | 5 => 2135096112984183 / 4000000000000
    | 6 => 1572702133272879 / 4000000000000
    | 7 => 2694851911212267 / 4000000000000
    | 8 => 1985015720764353 / 4000000000000
    | 9 => 3045524585354319 / 4000000000000
    | 10 => 1758334439177751 / 4000000000000
    | 11 => 3120195318142659 / 4000000000000
    | 12 => 2915291207300271 / 4000000000000
    | 13 => 2080489365509343 / 4000000000000
    | 14 => 2359053199908297 / 4000000000000
    | 15 => 1966732614423993 / 4000000000000
    | 16 => 1737667909859853 / 4000000000000
    | 17 => 503643889137447 / 800000000000
    | 18 => 1393105502679909 / 4000000000000
    | 19 => 1180950962842749 / 4000000000000
    | 20 => 738984279235647 / 4000000000000
    | 21 => 397428203123649 / 4000000000000
    | 22 => 1079094882277947 / 4000000000000
    | 23 => 1473411807091419 / 4000000000000
    | 24 => 623015720764353 / 4000000000000
    | 25 => 2532524316108513 / 4000000000000
    | _ => 1691608875692367 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39442170184 / 1000000000000) (39442191328 / 1000000000000), orderedInterval (-17777256735 / 1000000000000) (-17777235590 / 1000000000000))
    | 1 => (orderedInterval (13353020204 / 1000000000000) (13353020205 / 1000000000000), orderedInterval (48552683077 / 1000000000000) (48552683078 / 1000000000000))
    | 2 => (orderedInterval (-34463761509 / 1000000000000) (-34463761508 / 1000000000000), orderedInterval (-19504236656 / 1000000000000) (-19504236655 / 1000000000000))
    | 3 => (orderedInterval (-92323933191 / 1000000000000) (-92323932986 / 1000000000000), orderedInterval (13850294792 / 1000000000000) (13850294998 / 1000000000000))
    | 4 => (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))
    | 5 => (orderedInterval (16205610725 / 1000000000000) (16205610726 / 1000000000000), orderedInterval (30481623479 / 1000000000000) (30481623480 / 1000000000000))
    | 6 => (orderedInterval (-38329921730 / 1000000000000) (-38329921727 / 1000000000000), orderedInterval (-12198315675 / 1000000000000) (-12198315672 / 1000000000000))
    | 7 => (orderedInterval (24900718445 / 1000000000000) (24900741032 / 1000000000000), orderedInterval (-18043354360 / 1000000000000) (-18043331774 / 1000000000000))
    | 8 => (orderedInterval (22169770686 / 1000000000000) (22169770687 / 1000000000000), orderedInterval (28108646924 / 1000000000000) (28108646925 / 1000000000000))
    | 9 => (orderedInterval (27354257896 / 1000000000000) (27354321029 / 1000000000000), orderedInterval (-9392467794 / 1000000000000) (-9392404661 / 1000000000000))
    | 10 => (orderedInterval (19753208275 / 1000000000000) (19753208276 / 1000000000000), orderedInterval (32505133100 / 1000000000000) (32505133101 / 1000000000000))
    | 11 => (orderedInterval (28254405130 / 1000000000000) (28254418068 / 1000000000000), orderedInterval (-4239036352 / 1000000000000) (-4239023413 / 1000000000000))
    | 12 => (orderedInterval (20329530968 / 1000000000000) (20329530969 / 1000000000000), orderedInterval (21438340995 / 1000000000000) (21438340996 / 1000000000000))
    | 13 => (orderedInterval (-19664111949 / 1000000000000) (-19664110584 / 1000000000000), orderedInterval (28955104193 / 1000000000000) (28955105558 / 1000000000000))
    | 14 => (orderedInterval (-2328537588 / 1000000000000) (-2328537587 / 1000000000000), orderedInterval (32774339325 / 1000000000000) (32774339326 / 1000000000000))
    | 15 => (orderedInterval (24835031670 / 1000000000000) (24835041097 / 1000000000000), orderedInterval (-26063643912 / 1000000000000) (-26063634485 / 1000000000000))
    | 16 => (orderedInterval (38121128564 / 1000000000000) (38121129635 / 1000000000000), orderedInterval (-3541935612 / 1000000000000) (-3541934542 / 1000000000000))
    | 17 => (orderedInterval (28623748298 / 1000000000000) (28623848010 / 1000000000000), orderedInterval (-13875579147 / 1000000000000) (-13875479436 / 1000000000000))
    | 18 => (orderedInterval (-14444423839 / 1000000000000) (-14444423838 / 1000000000000), orderedInterval (-40219485896 / 1000000000000) (-40219485895 / 1000000000000))
    | 19 => (orderedInterval (30374205883 / 1000000000000) (30374205884 / 1000000000000), orderedInterval (35072674546 / 1000000000000) (35072674547 / 1000000000000))
    | 20 => (orderedInterval (-10325933709 / 1000000000000) (-10325933708 / 1000000000000), orderedInterval (-57758771614 / 1000000000000) (-57758771613 / 1000000000000))
    | 21 => (orderedInterval (-30415712472 / 1000000000000) (-30415711021 / 1000000000000), orderedInterval (74195857717 / 1000000000000) (74195859168 / 1000000000000))
    | 22 => (orderedInterval (18094671789 / 1000000000000) (18094671790 / 1000000000000), orderedInterval (45048771375 / 1000000000000) (45048771376 / 1000000000000))
    | 23 => (orderedInterval (-41572641443 / 1000000000000) (-41572641217 / 1000000000000), orderedInterval (92756121 / 1000000000000) (92756347 / 1000000000000))
    | 24 => (orderedInterval (-32930506009 / 1000000000000) (-32930500400 / 1000000000000), orderedInterval (54904751794 / 1000000000000) (54904757403 / 1000000000000))
    | 25 => (orderedInterval (-20072631897 / 1000000000000) (-20072629944 / 1000000000000), orderedInterval (24563758567 / 1000000000000) (24563760520 / 1000000000000))
    | _ => (orderedInterval (16092522277 / 1000000000000) (16092522590 / 1000000000000), orderedInterval (-35323285003 / 1000000000000) (-35323284690 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13735546926 / 1000000000000) (13735555331 / 1000000000000)
      | 1 => orderedInterval (931727478 / 1000000000000) (931727699 / 1000000000000)
      | 2 => orderedInterval (-232238875 / 1000000000000) (-232238158 / 1000000000000)
      | 3 => orderedInterval (619547710 / 1000000000000) (619560902 / 1000000000000)
      | 4 => orderedInterval (-2214721833 / 1000000000000) (-2214721663 / 1000000000000)
      | 5 => orderedInterval (-1161877819 / 1000000000000) (-1161875062 / 1000000000000)
      | 6 => orderedInterval (254211871 / 1000000000000) (254211957 / 1000000000000)
      | 7 => orderedInterval (3337198566 / 1000000000000) (3337198651 / 1000000000000)
      | _ => orderedInterval (-1583952316 / 1000000000000) (-1583951970 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8076169406 / 1000000000000) (-8076160997 / 1000000000000)
      | 1 => orderedInterval (-4454857827 / 1000000000000) (-4454857677 / 1000000000000)
      | 2 => orderedInterval (2091221573 / 1000000000000) (2091222985 / 1000000000000)
      | 3 => orderedInterval (5460493761 / 1000000000000) (5460523339 / 1000000000000)
      | 4 => orderedInterval (3066795774 / 1000000000000) (3066796038 / 1000000000000)
      | 5 => orderedInterval (-832870522 / 1000000000000) (-832865519 / 1000000000000)
      | 6 => orderedInterval (3836197333 / 1000000000000) (3836197413 / 1000000000000)
      | 7 => orderedInterval (-1217192512 / 1000000000000) (-1217192448 / 1000000000000)
      | _ => orderedInterval (4664920846 / 1000000000000) (4664921363 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12808600987 / 1000000000000) (-12808592551 / 1000000000000)
      | 1 => orderedInterval (2437180905 / 1000000000000) (2437181030 / 1000000000000)
      | 2 => orderedInterval (1862525675 / 1000000000000) (1862528466 / 1000000000000)
      | 3 => orderedInterval (767806129 / 1000000000000) (767872557 / 1000000000000)
      | 4 => orderedInterval (5975930349 / 1000000000000) (5975930760 / 1000000000000)
      | 5 => orderedInterval (450048744 / 1000000000000) (450057883 / 1000000000000)
      | 6 => orderedInterval (-1036055322 / 1000000000000) (-1036055246 / 1000000000000)
      | 7 => orderedInterval (-3515202944 / 1000000000000) (-3515202885 / 1000000000000)
      | _ => orderedInterval (-963798707 / 1000000000000) (-963797863 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8836588766 / 1000000000000) (8836597208 / 1000000000000)
      | 1 => orderedInterval (8683849601 / 1000000000000) (8683849732 / 1000000000000)
      | 2 => orderedInterval (-6419298371 / 1000000000000) (-6419292859 / 1000000000000)
      | 3 => orderedInterval (-16598258922 / 1000000000000) (-16598109880 / 1000000000000)
      | 4 => orderedInterval (-5119436062 / 1000000000000) (-5119435416 / 1000000000000)
      | 5 => orderedInterval (2729418372 / 1000000000000) (2729435098 / 1000000000000)
      | 6 => orderedInterval (-5284071604 / 1000000000000) (-5284071531 / 1000000000000)
      | 7 => orderedInterval (561634169 / 1000000000000) (561634230 / 1000000000000)
      | _ => orderedInterval (128117213 / 1000000000000) (128118654 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11548928261 / 1000000000000) (11548936733 / 1000000000000)
      | 1 => orderedInterval (-6885787416 / 1000000000000) (-6885787247 / 1000000000000)
      | 2 => orderedInterval (-9315893934 / 1000000000000) (-9315883026 / 1000000000000)
      | 3 => orderedInterval (-6721211177 / 1000000000000) (-6720876287 / 1000000000000)
      | 4 => orderedInterval (-17691419473 / 1000000000000) (-17691418446 / 1000000000000)
      | 5 => orderedInterval (4015384611 / 1000000000000) (4015415350 / 1000000000000)
      | 6 => orderedInterval (1558053598 / 1000000000000) (1558053671 / 1000000000000)
      | 7 => orderedInterval (4202587730 / 1000000000000) (4202587794 / 1000000000000)
      | _ => orderedInterval (12337717198 / 1000000000000) (12337719730 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13685441708 / 1000000000000) (13685467687 / 1000000000000)
    | 1 => orderedInterval (4538539020 / 1000000000000) (4538584497 / 1000000000000)
    | 2 => orderedInterval (-6830166158 / 1000000000000) (-6830077849 / 1000000000000)
    | 3 => orderedInterval (-12481456838 / 1000000000000) (-12481274764 / 1000000000000)
    | _ => orderedInterval (-6951640602 / 1000000000000) (-6951251728 / 1000000000000)

theorem compactCertificate469_stateChecks0 :
    compactCertificate469.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (681 / 2)) (orderedInterval (39442170184 / 1000000000000) (39442191328 / 1000000000000), orderedInterval (-17777256735 / 1000000000000) (-17777235590 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1003243035520581 / 4000000000000)) (orderedInterval (13353020204 / 1000000000000) (13353020205 / 1000000000000), orderedInterval (48552683077 / 1000000000000) (48552683078 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (324428184758373 / 800000000000)) (orderedInterval (-34463761509 / 1000000000000) (-34463761508 / 1000000000000), orderedInterval (-19504236656 / 1000000000000) (-19504236655 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks1 :
    compactCertificate469.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (292743815641167 / 4000000000000)) (orderedInterval (-92323933191 / 1000000000000) (-92323932986 / 1000000000000), orderedInterval (13850294792 / 1000000000000) (13850294998 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (786351066636099 / 4000000000000)) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2135096112984183 / 4000000000000)) (orderedInterval (16205610725 / 1000000000000) (16205610726 / 1000000000000), orderedInterval (30481623479 / 1000000000000) (30481623480 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks2 :
    compactCertificate469.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1572702133272879 / 4000000000000)) (orderedInterval (-38329921730 / 1000000000000) (-38329921727 / 1000000000000), orderedInterval (-12198315675 / 1000000000000) (-12198315672 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2694851911212267 / 4000000000000)) (orderedInterval (24900718445 / 1000000000000) (24900741032 / 1000000000000), orderedInterval (-18043354360 / 1000000000000) (-18043331774 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1985015720764353 / 4000000000000)) (orderedInterval (22169770686 / 1000000000000) (22169770687 / 1000000000000), orderedInterval (28108646924 / 1000000000000) (28108646925 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks3 :
    compactCertificate469.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3045524585354319 / 4000000000000)) (orderedInterval (27354257896 / 1000000000000) (27354321029 / 1000000000000), orderedInterval (-9392467794 / 1000000000000) (-9392404661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1758334439177751 / 4000000000000)) (orderedInterval (19753208275 / 1000000000000) (19753208276 / 1000000000000), orderedInterval (32505133100 / 1000000000000) (32505133101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3120195318142659 / 4000000000000)) (orderedInterval (28254405130 / 1000000000000) (28254418068 / 1000000000000), orderedInterval (-4239036352 / 1000000000000) (-4239023413 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks4 :
    compactCertificate469.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2915291207300271 / 4000000000000)) (orderedInterval (20329530968 / 1000000000000) (20329530969 / 1000000000000), orderedInterval (21438340995 / 1000000000000) (21438340996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2080489365509343 / 4000000000000)) (orderedInterval (-19664111949 / 1000000000000) (-19664110584 / 1000000000000), orderedInterval (28955104193 / 1000000000000) (28955105558 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2359053199908297 / 4000000000000)) (orderedInterval (-2328537588 / 1000000000000) (-2328537587 / 1000000000000), orderedInterval (32774339325 / 1000000000000) (32774339326 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks5 :
    compactCertificate469.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1966732614423993 / 4000000000000)) (orderedInterval (24835031670 / 1000000000000) (24835041097 / 1000000000000), orderedInterval (-26063643912 / 1000000000000) (-26063634485 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1737667909859853 / 4000000000000)) (orderedInterval (38121128564 / 1000000000000) (38121129635 / 1000000000000), orderedInterval (-3541935612 / 1000000000000) (-3541934542 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (503643889137447 / 800000000000)) (orderedInterval (28623748298 / 1000000000000) (28623848010 / 1000000000000), orderedInterval (-13875579147 / 1000000000000) (-13875479436 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks6 :
    compactCertificate469.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1393105502679909 / 4000000000000)) (orderedInterval (-14444423839 / 1000000000000) (-14444423838 / 1000000000000), orderedInterval (-40219485896 / 1000000000000) (-40219485895 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1180950962842749 / 4000000000000)) (orderedInterval (30374205883 / 1000000000000) (30374205884 / 1000000000000), orderedInterval (35072674546 / 1000000000000) (35072674547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (738984279235647 / 4000000000000)) (orderedInterval (-10325933709 / 1000000000000) (-10325933708 / 1000000000000), orderedInterval (-57758771614 / 1000000000000) (-57758771613 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks7 :
    compactCertificate469.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (397428203123649 / 4000000000000)) (orderedInterval (-30415712472 / 1000000000000) (-30415711021 / 1000000000000), orderedInterval (74195857717 / 1000000000000) (74195859168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1079094882277947 / 4000000000000)) (orderedInterval (18094671789 / 1000000000000) (18094671790 / 1000000000000), orderedInterval (45048771375 / 1000000000000) (45048771376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1473411807091419 / 4000000000000)) (orderedInterval (-41572641443 / 1000000000000) (-41572641217 / 1000000000000), orderedInterval (92756121 / 1000000000000) (92756347 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_stateChecks8 :
    compactCertificate469.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (623015720764353 / 4000000000000)) (orderedInterval (-32930506009 / 1000000000000) (-32930500400 / 1000000000000), orderedInterval (54904751794 / 1000000000000) (54904757403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2532524316108513 / 4000000000000)) (orderedInterval (-20072631897 / 1000000000000) (-20072629944 / 1000000000000), orderedInterval (24563758567 / 1000000000000) (24563760520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1691608875692367 / 4000000000000)) (orderedInterval (16092522277 / 1000000000000) (16092522590 / 1000000000000), orderedInterval (-35323285003 / 1000000000000) (-35323284690 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_states : ∀ j,
    BesselStateValid (compactCertificate469.point j) (compactCertificate469.state j) :=
  compactCertificate469.statesValid_of_checks3 compactCertificate469_stateChecks0
    compactCertificate469_stateChecks1 compactCertificate469_stateChecks2
    compactCertificate469_stateChecks3 compactCertificate469_stateChecks4
    compactCertificate469_stateChecks5 compactCertificate469_stateChecks6
    compactCertificate469_stateChecks7 compactCertificate469_stateChecks8

theorem compactCertificate469_chunkChecks0_0 :
    compactCertificate469.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (681 / 2) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39442170184 / 1000000000000) (39442191328 / 1000000000000), orderedInterval (-17777256735 / 1000000000000) (-17777235590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1003243035520581 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13353020204 / 1000000000000) (13353020205 / 1000000000000), orderedInterval (48552683077 / 1000000000000) (48552683078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (324428184758373 / 800000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34463761509 / 1000000000000) (-34463761508 / 1000000000000), orderedInterval (-19504236656 / 1000000000000) (-19504236655 / 1000000000000)))) (orderedInterval (13735546926 / 1000000000000) (13735555331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (292743815641167 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92323933191 / 1000000000000) (-92323932986 / 1000000000000), orderedInterval (13850294792 / 1000000000000) (13850294998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2135096112984183 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16205610725 / 1000000000000) (16205610726 / 1000000000000), orderedInterval (30481623479 / 1000000000000) (30481623480 / 1000000000000)))) (orderedInterval (931727478 / 1000000000000) (931727699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1572702133272879 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38329921730 / 1000000000000) (-38329921727 / 1000000000000), orderedInterval (-12198315675 / 1000000000000) (-12198315672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2694851911212267 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24900718445 / 1000000000000) (24900741032 / 1000000000000), orderedInterval (-18043354360 / 1000000000000) (-18043331774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1985015720764353 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22169770686 / 1000000000000) (22169770687 / 1000000000000), orderedInterval (28108646924 / 1000000000000) (28108646925 / 1000000000000)))) (orderedInterval (-232238875 / 1000000000000) (-232238158 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks0_1 :
    compactCertificate469.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3045524585354319 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27354257896 / 1000000000000) (27354321029 / 1000000000000), orderedInterval (-9392467794 / 1000000000000) (-9392404661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1758334439177751 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19753208275 / 1000000000000) (19753208276 / 1000000000000), orderedInterval (32505133100 / 1000000000000) (32505133101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3120195318142659 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28254405130 / 1000000000000) (28254418068 / 1000000000000), orderedInterval (-4239036352 / 1000000000000) (-4239023413 / 1000000000000)))) (orderedInterval (619547710 / 1000000000000) (619560902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2915291207300271 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20329530968 / 1000000000000) (20329530969 / 1000000000000), orderedInterval (21438340995 / 1000000000000) (21438340996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2080489365509343 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19664111949 / 1000000000000) (-19664110584 / 1000000000000), orderedInterval (28955104193 / 1000000000000) (28955105558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2359053199908297 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2328537588 / 1000000000000) (-2328537587 / 1000000000000), orderedInterval (32774339325 / 1000000000000) (32774339326 / 1000000000000)))) (orderedInterval (-2214721833 / 1000000000000) (-2214721663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1966732614423993 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24835031670 / 1000000000000) (24835041097 / 1000000000000), orderedInterval (-26063643912 / 1000000000000) (-26063634485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1737667909859853 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38121128564 / 1000000000000) (38121129635 / 1000000000000), orderedInterval (-3541935612 / 1000000000000) (-3541934542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (503643889137447 / 800000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28623748298 / 1000000000000) (28623848010 / 1000000000000), orderedInterval (-13875579147 / 1000000000000) (-13875479436 / 1000000000000)))) (orderedInterval (-1161877819 / 1000000000000) (-1161875062 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks0_2 :
    compactCertificate469.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1393105502679909 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14444423839 / 1000000000000) (-14444423838 / 1000000000000), orderedInterval (-40219485896 / 1000000000000) (-40219485895 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1180950962842749 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30374205883 / 1000000000000) (30374205884 / 1000000000000), orderedInterval (35072674546 / 1000000000000) (35072674547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (738984279235647 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10325933709 / 1000000000000) (-10325933708 / 1000000000000), orderedInterval (-57758771614 / 1000000000000) (-57758771613 / 1000000000000)))) (orderedInterval (254211871 / 1000000000000) (254211957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (397428203123649 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30415712472 / 1000000000000) (-30415711021 / 1000000000000), orderedInterval (74195857717 / 1000000000000) (74195859168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1079094882277947 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18094671789 / 1000000000000) (18094671790 / 1000000000000), orderedInterval (45048771375 / 1000000000000) (45048771376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1473411807091419 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41572641443 / 1000000000000) (-41572641217 / 1000000000000), orderedInterval (92756121 / 1000000000000) (92756347 / 1000000000000)))) (orderedInterval (3337198566 / 1000000000000) (3337198651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (623015720764353 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32930506009 / 1000000000000) (-32930500400 / 1000000000000), orderedInterval (54904751794 / 1000000000000) (54904757403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2532524316108513 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20072631897 / 1000000000000) (-20072629944 / 1000000000000), orderedInterval (24563758567 / 1000000000000) (24563760520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1691608875692367 / 4000000000000) 0 (IntervalRat.scale (681 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16092522277 / 1000000000000) (16092522590 / 1000000000000), orderedInterval (-35323285003 / 1000000000000) (-35323284690 / 1000000000000)))) (orderedInterval (-1583952316 / 1000000000000) (-1583951970 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks0 :
    compactCertificate469.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate469.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate469_chunkChecks0_0
    compactCertificate469_chunkChecks0_1 compactCertificate469_chunkChecks0_2

theorem compactCertificate469_chunkChecks1_0 :
    compactCertificate469.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (681 / 2) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39442170184 / 1000000000000) (39442191328 / 1000000000000), orderedInterval (-17777256735 / 1000000000000) (-17777235590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1003243035520581 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13353020204 / 1000000000000) (13353020205 / 1000000000000), orderedInterval (48552683077 / 1000000000000) (48552683078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (324428184758373 / 800000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34463761509 / 1000000000000) (-34463761508 / 1000000000000), orderedInterval (-19504236656 / 1000000000000) (-19504236655 / 1000000000000)))) (orderedInterval (-8076169406 / 1000000000000) (-8076160997 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (292743815641167 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92323933191 / 1000000000000) (-92323932986 / 1000000000000), orderedInterval (13850294792 / 1000000000000) (13850294998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2135096112984183 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16205610725 / 1000000000000) (16205610726 / 1000000000000), orderedInterval (30481623479 / 1000000000000) (30481623480 / 1000000000000)))) (orderedInterval (-4454857827 / 1000000000000) (-4454857677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1572702133272879 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38329921730 / 1000000000000) (-38329921727 / 1000000000000), orderedInterval (-12198315675 / 1000000000000) (-12198315672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2694851911212267 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24900718445 / 1000000000000) (24900741032 / 1000000000000), orderedInterval (-18043354360 / 1000000000000) (-18043331774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1985015720764353 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22169770686 / 1000000000000) (22169770687 / 1000000000000), orderedInterval (28108646924 / 1000000000000) (28108646925 / 1000000000000)))) (orderedInterval (2091221573 / 1000000000000) (2091222985 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks1_1 :
    compactCertificate469.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3045524585354319 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27354257896 / 1000000000000) (27354321029 / 1000000000000), orderedInterval (-9392467794 / 1000000000000) (-9392404661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1758334439177751 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19753208275 / 1000000000000) (19753208276 / 1000000000000), orderedInterval (32505133100 / 1000000000000) (32505133101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3120195318142659 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28254405130 / 1000000000000) (28254418068 / 1000000000000), orderedInterval (-4239036352 / 1000000000000) (-4239023413 / 1000000000000)))) (orderedInterval (5460493761 / 1000000000000) (5460523339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2915291207300271 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20329530968 / 1000000000000) (20329530969 / 1000000000000), orderedInterval (21438340995 / 1000000000000) (21438340996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2080489365509343 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19664111949 / 1000000000000) (-19664110584 / 1000000000000), orderedInterval (28955104193 / 1000000000000) (28955105558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2359053199908297 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2328537588 / 1000000000000) (-2328537587 / 1000000000000), orderedInterval (32774339325 / 1000000000000) (32774339326 / 1000000000000)))) (orderedInterval (3066795774 / 1000000000000) (3066796038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1966732614423993 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24835031670 / 1000000000000) (24835041097 / 1000000000000), orderedInterval (-26063643912 / 1000000000000) (-26063634485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1737667909859853 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38121128564 / 1000000000000) (38121129635 / 1000000000000), orderedInterval (-3541935612 / 1000000000000) (-3541934542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (503643889137447 / 800000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28623748298 / 1000000000000) (28623848010 / 1000000000000), orderedInterval (-13875579147 / 1000000000000) (-13875479436 / 1000000000000)))) (orderedInterval (-832870522 / 1000000000000) (-832865519 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks1_2 :
    compactCertificate469.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1393105502679909 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14444423839 / 1000000000000) (-14444423838 / 1000000000000), orderedInterval (-40219485896 / 1000000000000) (-40219485895 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1180950962842749 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30374205883 / 1000000000000) (30374205884 / 1000000000000), orderedInterval (35072674546 / 1000000000000) (35072674547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (738984279235647 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10325933709 / 1000000000000) (-10325933708 / 1000000000000), orderedInterval (-57758771614 / 1000000000000) (-57758771613 / 1000000000000)))) (orderedInterval (3836197333 / 1000000000000) (3836197413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (397428203123649 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30415712472 / 1000000000000) (-30415711021 / 1000000000000), orderedInterval (74195857717 / 1000000000000) (74195859168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1079094882277947 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18094671789 / 1000000000000) (18094671790 / 1000000000000), orderedInterval (45048771375 / 1000000000000) (45048771376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1473411807091419 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41572641443 / 1000000000000) (-41572641217 / 1000000000000), orderedInterval (92756121 / 1000000000000) (92756347 / 1000000000000)))) (orderedInterval (-1217192512 / 1000000000000) (-1217192448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (623015720764353 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32930506009 / 1000000000000) (-32930500400 / 1000000000000), orderedInterval (54904751794 / 1000000000000) (54904757403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2532524316108513 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20072631897 / 1000000000000) (-20072629944 / 1000000000000), orderedInterval (24563758567 / 1000000000000) (24563760520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1691608875692367 / 4000000000000) 1 (IntervalRat.scale (681 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16092522277 / 1000000000000) (16092522590 / 1000000000000), orderedInterval (-35323285003 / 1000000000000) (-35323284690 / 1000000000000)))) (orderedInterval (4664920846 / 1000000000000) (4664921363 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks1 :
    compactCertificate469.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate469.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate469_chunkChecks1_0
    compactCertificate469_chunkChecks1_1 compactCertificate469_chunkChecks1_2

theorem compactCertificate469_chunkChecks2_0 :
    compactCertificate469.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (681 / 2) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39442170184 / 1000000000000) (39442191328 / 1000000000000), orderedInterval (-17777256735 / 1000000000000) (-17777235590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1003243035520581 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13353020204 / 1000000000000) (13353020205 / 1000000000000), orderedInterval (48552683077 / 1000000000000) (48552683078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (324428184758373 / 800000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34463761509 / 1000000000000) (-34463761508 / 1000000000000), orderedInterval (-19504236656 / 1000000000000) (-19504236655 / 1000000000000)))) (orderedInterval (-12808600987 / 1000000000000) (-12808592551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (292743815641167 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92323933191 / 1000000000000) (-92323932986 / 1000000000000), orderedInterval (13850294792 / 1000000000000) (13850294998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2135096112984183 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16205610725 / 1000000000000) (16205610726 / 1000000000000), orderedInterval (30481623479 / 1000000000000) (30481623480 / 1000000000000)))) (orderedInterval (2437180905 / 1000000000000) (2437181030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1572702133272879 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38329921730 / 1000000000000) (-38329921727 / 1000000000000), orderedInterval (-12198315675 / 1000000000000) (-12198315672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2694851911212267 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24900718445 / 1000000000000) (24900741032 / 1000000000000), orderedInterval (-18043354360 / 1000000000000) (-18043331774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1985015720764353 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22169770686 / 1000000000000) (22169770687 / 1000000000000), orderedInterval (28108646924 / 1000000000000) (28108646925 / 1000000000000)))) (orderedInterval (1862525675 / 1000000000000) (1862528466 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks2_1 :
    compactCertificate469.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3045524585354319 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27354257896 / 1000000000000) (27354321029 / 1000000000000), orderedInterval (-9392467794 / 1000000000000) (-9392404661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1758334439177751 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19753208275 / 1000000000000) (19753208276 / 1000000000000), orderedInterval (32505133100 / 1000000000000) (32505133101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3120195318142659 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28254405130 / 1000000000000) (28254418068 / 1000000000000), orderedInterval (-4239036352 / 1000000000000) (-4239023413 / 1000000000000)))) (orderedInterval (767806129 / 1000000000000) (767872557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2915291207300271 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20329530968 / 1000000000000) (20329530969 / 1000000000000), orderedInterval (21438340995 / 1000000000000) (21438340996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2080489365509343 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19664111949 / 1000000000000) (-19664110584 / 1000000000000), orderedInterval (28955104193 / 1000000000000) (28955105558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2359053199908297 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2328537588 / 1000000000000) (-2328537587 / 1000000000000), orderedInterval (32774339325 / 1000000000000) (32774339326 / 1000000000000)))) (orderedInterval (5975930349 / 1000000000000) (5975930760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1966732614423993 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24835031670 / 1000000000000) (24835041097 / 1000000000000), orderedInterval (-26063643912 / 1000000000000) (-26063634485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1737667909859853 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38121128564 / 1000000000000) (38121129635 / 1000000000000), orderedInterval (-3541935612 / 1000000000000) (-3541934542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (503643889137447 / 800000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28623748298 / 1000000000000) (28623848010 / 1000000000000), orderedInterval (-13875579147 / 1000000000000) (-13875479436 / 1000000000000)))) (orderedInterval (450048744 / 1000000000000) (450057883 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks2_2 :
    compactCertificate469.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1393105502679909 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14444423839 / 1000000000000) (-14444423838 / 1000000000000), orderedInterval (-40219485896 / 1000000000000) (-40219485895 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1180950962842749 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30374205883 / 1000000000000) (30374205884 / 1000000000000), orderedInterval (35072674546 / 1000000000000) (35072674547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (738984279235647 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10325933709 / 1000000000000) (-10325933708 / 1000000000000), orderedInterval (-57758771614 / 1000000000000) (-57758771613 / 1000000000000)))) (orderedInterval (-1036055322 / 1000000000000) (-1036055246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (397428203123649 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30415712472 / 1000000000000) (-30415711021 / 1000000000000), orderedInterval (74195857717 / 1000000000000) (74195859168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1079094882277947 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18094671789 / 1000000000000) (18094671790 / 1000000000000), orderedInterval (45048771375 / 1000000000000) (45048771376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1473411807091419 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41572641443 / 1000000000000) (-41572641217 / 1000000000000), orderedInterval (92756121 / 1000000000000) (92756347 / 1000000000000)))) (orderedInterval (-3515202944 / 1000000000000) (-3515202885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (623015720764353 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32930506009 / 1000000000000) (-32930500400 / 1000000000000), orderedInterval (54904751794 / 1000000000000) (54904757403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2532524316108513 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20072631897 / 1000000000000) (-20072629944 / 1000000000000), orderedInterval (24563758567 / 1000000000000) (24563760520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1691608875692367 / 4000000000000) 2 (IntervalRat.scale (681 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16092522277 / 1000000000000) (16092522590 / 1000000000000), orderedInterval (-35323285003 / 1000000000000) (-35323284690 / 1000000000000)))) (orderedInterval (-963798707 / 1000000000000) (-963797863 / 1000000000000))) = true
  rfl'

theorem compactCertificate469_chunkChecks2 :
    compactCertificate469.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate469.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate469_chunkChecks2_0
    compactCertificate469_chunkChecks2_1 compactCertificate469_chunkChecks2_2

theorem compactCertificate469_chunkChecks3_0 :
    compactCertificate469.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (681 / 2) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39442170184 / 1000000000000) (39442191328 / 1000000000000), orderedInterval (-17777256735 / 1000000000000) (-17777235590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1003243035520581 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13353020204 / 1000000000000) (13353020205 / 1000000000000), orderedInterval (48552683077 / 1000000000000) (48552683078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (324428184758373 / 800000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34463761509 / 1000000000000) (-34463761508 / 1000000000000), orderedInterval (-19504236656 / 1000000000000) (-19504236655 / 1000000000000)))) (orderedInterval (8836588766 / 1000000000000) (8836597208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (292743815641167 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92323933191 / 1000000000000) (-92323932986 / 1000000000000), orderedInterval (13850294792 / 1000000000000) (13850294998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2135096112984183 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16205610725 / 1000000000000) (16205610726 / 1000000000000), orderedInterval (30481623479 / 1000000000000) (30481623480 / 1000000000000)))) (orderedInterval (8683849601 / 1000000000000) (8683849732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1572702133272879 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38329921730 / 1000000000000) (-38329921727 / 1000000000000), orderedInterval (-12198315675 / 1000000000000) (-12198315672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2694851911212267 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24900718445 / 1000000000000) (24900741032 / 1000000000000), orderedInterval (-18043354360 / 1000000000000) (-18043331774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1985015720764353 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22169770686 / 1000000000000) (22169770687 / 1000000000000), orderedInterval (28108646924 / 1000000000000) (28108646925 / 1000000000000)))) (orderedInterval (-6419298371 / 1000000000000) (-6419292859 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate469_chunkChecks3_1 :
    compactCertificate469.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3045524585354319 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27354257896 / 1000000000000) (27354321029 / 1000000000000), orderedInterval (-9392467794 / 1000000000000) (-9392404661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1758334439177751 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19753208275 / 1000000000000) (19753208276 / 1000000000000), orderedInterval (32505133100 / 1000000000000) (32505133101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3120195318142659 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28254405130 / 1000000000000) (28254418068 / 1000000000000), orderedInterval (-4239036352 / 1000000000000) (-4239023413 / 1000000000000)))) (orderedInterval (-16598258922 / 1000000000000) (-16598109880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2915291207300271 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20329530968 / 1000000000000) (20329530969 / 1000000000000), orderedInterval (21438340995 / 1000000000000) (21438340996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2080489365509343 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19664111949 / 1000000000000) (-19664110584 / 1000000000000), orderedInterval (28955104193 / 1000000000000) (28955105558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2359053199908297 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2328537588 / 1000000000000) (-2328537587 / 1000000000000), orderedInterval (32774339325 / 1000000000000) (32774339326 / 1000000000000)))) (orderedInterval (-5119436062 / 1000000000000) (-5119435416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1966732614423993 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24835031670 / 1000000000000) (24835041097 / 1000000000000), orderedInterval (-26063643912 / 1000000000000) (-26063634485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1737667909859853 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38121128564 / 1000000000000) (38121129635 / 1000000000000), orderedInterval (-3541935612 / 1000000000000) (-3541934542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (503643889137447 / 800000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28623748298 / 1000000000000) (28623848010 / 1000000000000), orderedInterval (-13875579147 / 1000000000000) (-13875479436 / 1000000000000)))) (orderedInterval (2729418372 / 1000000000000) (2729435098 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate469_chunkChecks3_2 :
    compactCertificate469.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1393105502679909 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14444423839 / 1000000000000) (-14444423838 / 1000000000000), orderedInterval (-40219485896 / 1000000000000) (-40219485895 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1180950962842749 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30374205883 / 1000000000000) (30374205884 / 1000000000000), orderedInterval (35072674546 / 1000000000000) (35072674547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (738984279235647 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10325933709 / 1000000000000) (-10325933708 / 1000000000000), orderedInterval (-57758771614 / 1000000000000) (-57758771613 / 1000000000000)))) (orderedInterval (-5284071604 / 1000000000000) (-5284071531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (397428203123649 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30415712472 / 1000000000000) (-30415711021 / 1000000000000), orderedInterval (74195857717 / 1000000000000) (74195859168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1079094882277947 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18094671789 / 1000000000000) (18094671790 / 1000000000000), orderedInterval (45048771375 / 1000000000000) (45048771376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1473411807091419 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41572641443 / 1000000000000) (-41572641217 / 1000000000000), orderedInterval (92756121 / 1000000000000) (92756347 / 1000000000000)))) (orderedInterval (561634169 / 1000000000000) (561634230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (623015720764353 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32930506009 / 1000000000000) (-32930500400 / 1000000000000), orderedInterval (54904751794 / 1000000000000) (54904757403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2532524316108513 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20072631897 / 1000000000000) (-20072629944 / 1000000000000), orderedInterval (24563758567 / 1000000000000) (24563760520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1691608875692367 / 4000000000000) 3 (IntervalRat.scale (681 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16092522277 / 1000000000000) (16092522590 / 1000000000000), orderedInterval (-35323285003 / 1000000000000) (-35323284690 / 1000000000000)))) (orderedInterval (128117213 / 1000000000000) (128118654 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate469_chunkChecks3 :
    compactCertificate469.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate469.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate469_chunkChecks3_0
    compactCertificate469_chunkChecks3_1 compactCertificate469_chunkChecks3_2

theorem compactCertificate469_chunkChecks4_0 :
    compactCertificate469.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (681 / 2) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39442170184 / 1000000000000) (39442191328 / 1000000000000), orderedInterval (-17777256735 / 1000000000000) (-17777235590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1003243035520581 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13353020204 / 1000000000000) (13353020205 / 1000000000000), orderedInterval (48552683077 / 1000000000000) (48552683078 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (324428184758373 / 800000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34463761509 / 1000000000000) (-34463761508 / 1000000000000), orderedInterval (-19504236656 / 1000000000000) (-19504236655 / 1000000000000)))) (orderedInterval (11548928261 / 1000000000000) (11548936733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (292743815641167 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-92323933191 / 1000000000000) (-92323932986 / 1000000000000), orderedInterval (13850294792 / 1000000000000) (13850294998 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (786351066636099 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (29637841273 / 1000000000000) (29637846124 / 1000000000000), orderedInterval (-48654718463 / 1000000000000) (-48654713612 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2135096112984183 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (16205610725 / 1000000000000) (16205610726 / 1000000000000), orderedInterval (30481623479 / 1000000000000) (30481623480 / 1000000000000)))) (orderedInterval (-6885787416 / 1000000000000) (-6885787247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1572702133272879 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38329921730 / 1000000000000) (-38329921727 / 1000000000000), orderedInterval (-12198315675 / 1000000000000) (-12198315672 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2694851911212267 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24900718445 / 1000000000000) (24900741032 / 1000000000000), orderedInterval (-18043354360 / 1000000000000) (-18043331774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1985015720764353 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22169770686 / 1000000000000) (22169770687 / 1000000000000), orderedInterval (28108646924 / 1000000000000) (28108646925 / 1000000000000)))) (orderedInterval (-9315893934 / 1000000000000) (-9315883026 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate469_chunkChecks4_1 :
    compactCertificate469.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3045524585354319 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27354257896 / 1000000000000) (27354321029 / 1000000000000), orderedInterval (-9392467794 / 1000000000000) (-9392404661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1758334439177751 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19753208275 / 1000000000000) (19753208276 / 1000000000000), orderedInterval (32505133100 / 1000000000000) (32505133101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3120195318142659 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28254405130 / 1000000000000) (28254418068 / 1000000000000), orderedInterval (-4239036352 / 1000000000000) (-4239023413 / 1000000000000)))) (orderedInterval (-6721211177 / 1000000000000) (-6720876287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2915291207300271 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20329530968 / 1000000000000) (20329530969 / 1000000000000), orderedInterval (21438340995 / 1000000000000) (21438340996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2080489365509343 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19664111949 / 1000000000000) (-19664110584 / 1000000000000), orderedInterval (28955104193 / 1000000000000) (28955105558 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2359053199908297 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2328537588 / 1000000000000) (-2328537587 / 1000000000000), orderedInterval (32774339325 / 1000000000000) (32774339326 / 1000000000000)))) (orderedInterval (-17691419473 / 1000000000000) (-17691418446 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1966732614423993 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24835031670 / 1000000000000) (24835041097 / 1000000000000), orderedInterval (-26063643912 / 1000000000000) (-26063634485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1737667909859853 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38121128564 / 1000000000000) (38121129635 / 1000000000000), orderedInterval (-3541935612 / 1000000000000) (-3541934542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (503643889137447 / 800000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28623748298 / 1000000000000) (28623848010 / 1000000000000), orderedInterval (-13875579147 / 1000000000000) (-13875479436 / 1000000000000)))) (orderedInterval (4015384611 / 1000000000000) (4015415350 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate469_chunkChecks4_2 :
    compactCertificate469.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1393105502679909 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-14444423839 / 1000000000000) (-14444423838 / 1000000000000), orderedInterval (-40219485896 / 1000000000000) (-40219485895 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1180950962842749 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30374205883 / 1000000000000) (30374205884 / 1000000000000), orderedInterval (35072674546 / 1000000000000) (35072674547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (738984279235647 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-10325933709 / 1000000000000) (-10325933708 / 1000000000000), orderedInterval (-57758771614 / 1000000000000) (-57758771613 / 1000000000000)))) (orderedInterval (1558053598 / 1000000000000) (1558053671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (397428203123649 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30415712472 / 1000000000000) (-30415711021 / 1000000000000), orderedInterval (74195857717 / 1000000000000) (74195859168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1079094882277947 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18094671789 / 1000000000000) (18094671790 / 1000000000000), orderedInterval (45048771375 / 1000000000000) (45048771376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1473411807091419 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41572641443 / 1000000000000) (-41572641217 / 1000000000000), orderedInterval (92756121 / 1000000000000) (92756347 / 1000000000000)))) (orderedInterval (4202587730 / 1000000000000) (4202587794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (623015720764353 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32930506009 / 1000000000000) (-32930500400 / 1000000000000), orderedInterval (54904751794 / 1000000000000) (54904757403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2532524316108513 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20072631897 / 1000000000000) (-20072629944 / 1000000000000), orderedInterval (24563758567 / 1000000000000) (24563760520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1691608875692367 / 4000000000000) 4 (IntervalRat.scale (681 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16092522277 / 1000000000000) (16092522590 / 1000000000000), orderedInterval (-35323285003 / 1000000000000) (-35323284690 / 1000000000000)))) (orderedInterval (12337717198 / 1000000000000) (12337719730 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate469_chunkChecks4 :
    compactCertificate469.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate469.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate469_chunkChecks4_0
    compactCertificate469_chunkChecks4_1 compactCertificate469_chunkChecks4_2

theorem compactCertificate469_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate469.chunkCheck r b = true :=
  compactCertificate469.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate469_chunkChecks0
    · exact compactCertificate469_chunkChecks1
    · exact compactCertificate469_chunkChecks2
    · exact compactCertificate469_chunkChecks3
    · exact compactCertificate469_chunkChecks4)

theorem compactCertificate469_coefficient0 :
    compactCertificate469.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate469_coefficient1 :
    compactCertificate469.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate469_coefficient2 :
    compactCertificate469.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate469_coefficient3 :
    compactCertificate469.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate469_coefficient4 :
    compactCertificate469.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate469_coefficients : ∀ r : Fin 5,
    compactCertificate469.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate469_coefficient0
  · exact compactCertificate469_coefficient1
  · exact compactCertificate469_coefficient2
  · exact compactCertificate469_coefficient3
  · exact compactCertificate469_coefficient4

theorem compactCertificate469_lower : (1 : ℚ) ≤ compactCertificate469.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate469, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate469_proves {t : ℝ} (ht : t ∈ compactCertificate469.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate469.proves compactCertificate469_states compactCertificate469_chunks
    compactCertificate469_coefficients compactCertificate469_lower ht

end Erdos232
