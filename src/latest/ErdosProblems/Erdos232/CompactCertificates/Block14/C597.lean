/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate597 : CompactCertificate where
  left := 468
  right := 469
  center := 937 / 2
  grid := fun i =>
    match i.val with
    | 0 => 149
    | 1 => 110
    | 2 => 178
    | 3 => 32
    | 4 => 86
    | 5 => 234
    | 6 => 172
    | 7 => 295
    | 8 => 217
    | 9 => 334
    | 10 => 193
    | 11 => 342
    | 12 => 319
    | 13 => 228
    | 14 => 258
    | 15 => 215
    | 16 => 190
    | 17 => 276
    | 18 => 153
    | 19 => 129
    | 20 => 81
    | 21 => 44
    | 22 => 118
    | 23 => 161
    | 24 => 68
    | 25 => 277
    | _ => 185
  point := fun i =>
    match i.val with
    | 0 => 937 / 2
    | 1 => 1380379918183237 / 4000000000000
    | 2 => 446386503845221 / 800000000000
    | 3 => 402791417409359 / 4000000000000
    | 4 => 1081954404461123 / 4000000000000
    | 5 => 2937716678217591 / 4000000000000
    | 6 => 2163908808923183 / 4000000000000
    | 7 => 3707894626734059 / 4000000000000
    | 8 => 2731218399935681 / 4000000000000
    | 9 => 4190391389834063 / 4000000000000
    | 10 => 2419323596930327 / 4000000000000
    | 11 => 4293132177826243 / 4000000000000
    | 12 => 4011200970984367 / 4000000000000
    | 13 => 2862582284114911 / 4000000000000
    | 14 => 3245863213383369 / 4000000000000
    | 15 => 2706062349067961 / 4000000000000
    | 16 => 2390888152039181 / 4000000000000
    | 17 => 692972575802919 / 800000000000
    | 18 => 1916798613819493 / 4000000000000
    | 19 => 1624891412898173 / 4000000000000
    | 20 => 1016781600064319 / 4000000000000
    | 21 => 546828526177473 / 4000000000000
    | 22 => 1484745821871419 / 4000000000000
    | 23 => 2027293484940763 / 4000000000000
    | 24 => 857218399935681 / 4000000000000
    | 25 => 3484545204396001 / 4000000000000
    | _ => 2327514708551759 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-34192163241 / 1000000000000) (-34192163239 / 1000000000000), orderedInterval (-13738207290 / 1000000000000) (-13738207288 / 1000000000000))
    | 1 => (orderedInterval (12890582840 / 1000000000000) (12890582841 / 1000000000000), orderedInterval (40952060223 / 1000000000000) (40952060224 / 1000000000000))
    | 2 => (orderedInterval (-14240023890 / 1000000000000) (-14240023751 / 1000000000000), orderedInterval (30642029849 / 1000000000000) (30642029988 / 1000000000000))
    | 3 => (orderedInterval (64723846748 / 1000000000000) (64723846749 / 1000000000000), orderedInterval (45861714243 / 1000000000000) (45861714244 / 1000000000000))
    | 4 => (orderedInterval (43160090012 / 1000000000000) (43160090013 / 1000000000000), orderedInterval (22074138200 / 1000000000000) (22074138201 / 1000000000000))
    | 5 => (orderedInterval (2403210286 / 1000000000000) (2403210287 / 1000000000000), orderedInterval (29341972018 / 1000000000000) (29341972019 / 1000000000000))
    | 6 => (orderedInterval (33853279599 / 1000000000000) (33853279678 / 1000000000000), orderedInterval (5514061825 / 1000000000000) (5514061905 / 1000000000000))
    | 7 => (orderedInterval (-21896044604 / 1000000000000) (-21896044601 / 1000000000000), orderedInterval (-14387336311 / 1000000000000) (-14387336308 / 1000000000000))
    | 8 => (orderedInterval (-29229608583 / 1000000000000) (-29229576611 / 1000000000000), orderedInterval (8852627527 / 1000000000000) (8852659499 / 1000000000000))
    | 9 => (orderedInterval (-19444558435 / 1000000000000) (-19444556168 / 1000000000000), orderedInterval (15161968307 / 1000000000000) (15161970574 / 1000000000000))
    | 10 => (orderedInterval (21179294539 / 1000000000000) (21179297592 / 1000000000000), orderedInterval (-24593834963 / 1000000000000) (-24593831910 / 1000000000000))
    | 11 => (orderedInterval (-8496541993 / 1000000000000) (-8496541992 / 1000000000000), orderedInterval (22828520087 / 1000000000000) (22828520089 / 1000000000000))
    | 12 => (orderedInterval (-24900445247 / 1000000000000) (-24900443477 / 1000000000000), orderedInterval (-3835942855 / 1000000000000) (-3835941085 / 1000000000000))
    | 13 => (orderedInterval (4388360500 / 1000000000000) (4388360501 / 1000000000000), orderedInterval (29498062955 / 1000000000000) (29498062956 / 1000000000000))
    | 14 => (orderedInterval (27697676536 / 1000000000000) (27697691795 / 1000000000000), orderedInterval (-4184658676 / 1000000000000) (-4184643416 / 1000000000000))
    | 15 => (orderedInterval (-29416372615 / 1000000000000) (-29416343175 / 1000000000000), orderedInterval (8722596807 / 1000000000000) (8722626247 / 1000000000000))
    | 16 => (orderedInterval (32616835749 / 1000000000000) (32616837185 / 1000000000000), orderedInterval (-1131021004 / 1000000000000) (-1131019568 / 1000000000000))
    | 17 => (orderedInterval (-2128607281 / 1000000000000) (-2128607280 / 1000000000000), orderedInterval (27027379649 / 1000000000000) (27027379650 / 1000000000000))
    | 18 => (orderedInterval (22887059325 / 1000000000000) (22887063602 / 1000000000000), orderedInterval (-28390921487 / 1000000000000) (-28390917210 / 1000000000000))
    | 19 => (orderedInterval (-39005397578 / 1000000000000) (-39005395294 / 1000000000000), orderedInterval (6811639734 / 1000000000000) (6811642018 / 1000000000000))
    | 20 => (orderedInterval (-24487378312 / 1000000000000) (-24487378311 / 1000000000000), orderedInterval (-43596091469 / 1000000000000) (-43596091468 / 1000000000000))
    | 21 => (orderedInterval (-45936260463 / 1000000000000) (-45936219187 / 1000000000000), orderedInterval (50632620428 / 1000000000000) (50632661705 / 1000000000000))
    | 22 => (orderedInterval (39474697912 / 1000000000000) (39474697914 / 1000000000000), orderedInterval (12470454041 / 1000000000000) (12470454043 / 1000000000000))
    | 23 => (orderedInterval (-34414583770 / 1000000000000) (-34414575540 / 1000000000000), orderedInterval (8503543108 / 1000000000000) (8503551337 / 1000000000000))
    | 24 => (orderedInterval (54175903410 / 1000000000000) (54175903424 / 1000000000000), orderedInterval (5839676922 / 1000000000000) (5839676937 / 1000000000000))
    | 25 => (orderedInterval (-26806488316 / 1000000000000) (-26806471434 / 1000000000000), orderedInterval (3508927324 / 1000000000000) (3508944205 / 1000000000000))
    | _ => (orderedInterval (-32906326907 / 1000000000000) (-32906326663 / 1000000000000), orderedInterval (-3325787026 / 1000000000000) (-3325786783 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14268082171 / 1000000000000) (-14268082129 / 1000000000000)
      | 1 => orderedInterval (702799011 / 1000000000000) (702799068 / 1000000000000)
      | 2 => orderedInterval (-31060361 / 1000000000000) (-31059562 / 1000000000000)
      | 3 => orderedInterval (3816440700 / 1000000000000) (3816441514 / 1000000000000)
      | 4 => orderedInterval (724339491 / 1000000000000) (724339656 / 1000000000000)
      | 5 => orderedInterval (-2260744547 / 1000000000000) (-2260744080 / 1000000000000)
      | 6 => orderedInterval (-2248958128 / 1000000000000) (-2248957197 / 1000000000000)
      | 7 => orderedInterval (2590154791 / 1000000000000) (2590156240 / 1000000000000)
      | _ => orderedInterval (8682784248 / 1000000000000) (8682785798 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-3022717534 / 1000000000000) (-3022717487 / 1000000000000)
      | 1 => orderedInterval (-2911532245 / 1000000000000) (-2911532181 / 1000000000000)
      | 2 => orderedInterval (1189846378 / 1000000000000) (1189847550 / 1000000000000)
      | 3 => orderedInterval (-942216543 / 1000000000000) (-942214965 / 1000000000000)
      | 4 => orderedInterval (4445817922 / 1000000000000) (4445818215 / 1000000000000)
      | 5 => orderedInterval (1507486987 / 1000000000000) (1507487648 / 1000000000000)
      | 6 => orderedInterval (3538812764 / 1000000000000) (3538813684 / 1000000000000)
      | 7 => orderedInterval (-1201974789 / 1000000000000) (-1201973834 / 1000000000000)
      | _ => orderedInterval (260007487 / 1000000000000) (260010281 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14679167856 / 1000000000000) (14679167911 / 1000000000000)
      | 1 => orderedInterval (-66793327 / 1000000000000) (-66793238 / 1000000000000)
      | 2 => orderedInterval (-1145977162 / 1000000000000) (-1145975436 / 1000000000000)
      | 3 => orderedInterval (-13549721595 / 1000000000000) (-13549718376 / 1000000000000)
      | 4 => orderedInterval (-2616798694 / 1000000000000) (-2616798165 / 1000000000000)
      | 5 => orderedInterval (3929618972 / 1000000000000) (3929619913 / 1000000000000)
      | 6 => orderedInterval (2395876408 / 1000000000000) (2395877326 / 1000000000000)
      | 7 => orderedInterval (-2594136740 / 1000000000000) (-2594135885 / 1000000000000)
      | _ => orderedInterval (-17137326844 / 1000000000000) (-17137321747 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (2223752585 / 1000000000000) (2223752649 / 1000000000000)
      | 1 => orderedInterval (7885529892 / 1000000000000) (7885530025 / 1000000000000)
      | 2 => orderedInterval (-4097236073 / 1000000000000) (-4097233529 / 1000000000000)
      | 3 => orderedInterval (-4946641963 / 1000000000000) (-4946635157 / 1000000000000)
      | 4 => orderedInterval (-10725665900 / 1000000000000) (-10725664930 / 1000000000000)
      | 5 => orderedInterval (-4819888656 / 1000000000000) (-4819887311 / 1000000000000)
      | 6 => orderedInterval (-4384750647 / 1000000000000) (-4384749728 / 1000000000000)
      | 7 => orderedInterval (994532451 / 1000000000000) (994533322 / 1000000000000)
      | _ => orderedInterval (673965058 / 1000000000000) (673974405 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-15207981062 / 1000000000000) (-15207980987 / 1000000000000)
      | 1 => orderedInterval (-891781610 / 1000000000000) (-891781405 / 1000000000000)
      | 2 => orderedInterval (7180917583 / 1000000000000) (7180921354 / 1000000000000)
      | 3 => orderedInterval (57488616273 / 1000000000000) (57488631011 / 1000000000000)
      | 4 => orderedInterval (10479373546 / 1000000000000) (10479375356 / 1000000000000)
      | 5 => orderedInterval (-7038593172 / 1000000000000) (-7038591235 / 1000000000000)
      | 6 => orderedInterval (-2807912677 / 1000000000000) (-2807911752 / 1000000000000)
      | 7 => orderedInterval (3261280473 / 1000000000000) (3261281400 / 1000000000000)
      | _ => orderedInterval (40787130536 / 1000000000000) (40787147776 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2292326966 / 1000000000000) (-2292320692 / 1000000000000)
    | 1 => orderedInterval (2863530427 / 1000000000000) (2863538911 / 1000000000000)
    | 2 => orderedInterval (-16106091126 / 1000000000000) (-16106077697 / 1000000000000)
    | 3 => orderedInterval (-17196403253 / 1000000000000) (-17196380254 / 1000000000000)
    | _ => orderedInterval (93251049890 / 1000000000000) (93251091518 / 1000000000000)

theorem compactCertificate597_stateChecks0 :
    compactCertificate597.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (937 / 2)) (orderedInterval (-34192163241 / 1000000000000) (-34192163239 / 1000000000000), orderedInterval (-13738207290 / 1000000000000) (-13738207288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1380379918183237 / 4000000000000)) (orderedInterval (12890582840 / 1000000000000) (12890582841 / 1000000000000), orderedInterval (40952060223 / 1000000000000) (40952060224 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (446386503845221 / 800000000000)) (orderedInterval (-14240023890 / 1000000000000) (-14240023751 / 1000000000000), orderedInterval (30642029849 / 1000000000000) (30642029988 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks1 :
    compactCertificate597.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (402791417409359 / 4000000000000)) (orderedInterval (64723846748 / 1000000000000) (64723846749 / 1000000000000), orderedInterval (45861714243 / 1000000000000) (45861714244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1081954404461123 / 4000000000000)) (orderedInterval (43160090012 / 1000000000000) (43160090013 / 1000000000000), orderedInterval (22074138200 / 1000000000000) (22074138201 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2937716678217591 / 4000000000000)) (orderedInterval (2403210286 / 1000000000000) (2403210287 / 1000000000000), orderedInterval (29341972018 / 1000000000000) (29341972019 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks2 :
    compactCertificate597.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2163908808923183 / 4000000000000)) (orderedInterval (33853279599 / 1000000000000) (33853279678 / 1000000000000), orderedInterval (5514061825 / 1000000000000) (5514061905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 295 12 (3707894626734059 / 4000000000000)) (orderedInterval (-21896044604 / 1000000000000) (-21896044601 / 1000000000000), orderedInterval (-14387336311 / 1000000000000) (-14387336308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2731218399935681 / 4000000000000)) (orderedInterval (-29229608583 / 1000000000000) (-29229576611 / 1000000000000), orderedInterval (8852627527 / 1000000000000) (8852659499 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks3 :
    compactCertificate597.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 334 12 (4190391389834063 / 4000000000000)) (orderedInterval (-19444558435 / 1000000000000) (-19444556168 / 1000000000000), orderedInterval (15161968307 / 1000000000000) (15161970574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2419323596930327 / 4000000000000)) (orderedInterval (21179294539 / 1000000000000) (21179297592 / 1000000000000), orderedInterval (-24593834963 / 1000000000000) (-24593831910 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 342 12 (4293132177826243 / 4000000000000)) (orderedInterval (-8496541993 / 1000000000000) (-8496541992 / 1000000000000), orderedInterval (22828520087 / 1000000000000) (22828520089 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks4 :
    compactCertificate597.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 319 12 (4011200970984367 / 4000000000000)) (orderedInterval (-24900445247 / 1000000000000) (-24900443477 / 1000000000000), orderedInterval (-3835942855 / 1000000000000) (-3835941085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2862582284114911 / 4000000000000)) (orderedInterval (4388360500 / 1000000000000) (4388360501 / 1000000000000), orderedInterval (29498062955 / 1000000000000) (29498062956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (3245863213383369 / 4000000000000)) (orderedInterval (27697676536 / 1000000000000) (27697691795 / 1000000000000), orderedInterval (-4184658676 / 1000000000000) (-4184643416 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks5 :
    compactCertificate597.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2706062349067961 / 4000000000000)) (orderedInterval (-29416372615 / 1000000000000) (-29416343175 / 1000000000000), orderedInterval (8722596807 / 1000000000000) (8722626247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2390888152039181 / 4000000000000)) (orderedInterval (32616835749 / 1000000000000) (32616837185 / 1000000000000), orderedInterval (-1131021004 / 1000000000000) (-1131019568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (692972575802919 / 800000000000)) (orderedInterval (-2128607281 / 1000000000000) (-2128607280 / 1000000000000), orderedInterval (27027379649 / 1000000000000) (27027379650 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks6 :
    compactCertificate597.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1916798613819493 / 4000000000000)) (orderedInterval (22887059325 / 1000000000000) (22887063602 / 1000000000000), orderedInterval (-28390921487 / 1000000000000) (-28390917210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1624891412898173 / 4000000000000)) (orderedInterval (-39005397578 / 1000000000000) (-39005395294 / 1000000000000), orderedInterval (6811639734 / 1000000000000) (6811642018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1016781600064319 / 4000000000000)) (orderedInterval (-24487378312 / 1000000000000) (-24487378311 / 1000000000000), orderedInterval (-43596091469 / 1000000000000) (-43596091468 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks7 :
    compactCertificate597.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (546828526177473 / 4000000000000)) (orderedInterval (-45936260463 / 1000000000000) (-45936219187 / 1000000000000), orderedInterval (50632620428 / 1000000000000) (50632661705 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1484745821871419 / 4000000000000)) (orderedInterval (39474697912 / 1000000000000) (39474697914 / 1000000000000), orderedInterval (12470454041 / 1000000000000) (12470454043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2027293484940763 / 4000000000000)) (orderedInterval (-34414583770 / 1000000000000) (-34414575540 / 1000000000000), orderedInterval (8503543108 / 1000000000000) (8503551337 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_stateChecks8 :
    compactCertificate597.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (857218399935681 / 4000000000000)) (orderedInterval (54175903410 / 1000000000000) (54175903424 / 1000000000000), orderedInterval (5839676922 / 1000000000000) (5839676937 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (3484545204396001 / 4000000000000)) (orderedInterval (-26806488316 / 1000000000000) (-26806471434 / 1000000000000), orderedInterval (3508927324 / 1000000000000) (3508944205 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2327514708551759 / 4000000000000)) (orderedInterval (-32906326907 / 1000000000000) (-32906326663 / 1000000000000), orderedInterval (-3325787026 / 1000000000000) (-3325786783 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_states : ∀ j,
    BesselStateValid (compactCertificate597.point j) (compactCertificate597.state j) :=
  compactCertificate597.statesValid_of_checks3 compactCertificate597_stateChecks0
    compactCertificate597_stateChecks1 compactCertificate597_stateChecks2
    compactCertificate597_stateChecks3 compactCertificate597_stateChecks4
    compactCertificate597_stateChecks5 compactCertificate597_stateChecks6
    compactCertificate597_stateChecks7 compactCertificate597_stateChecks8

theorem compactCertificate597_chunkChecks0_0 :
    compactCertificate597.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (937 / 2) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34192163241 / 1000000000000) (-34192163239 / 1000000000000), orderedInterval (-13738207290 / 1000000000000) (-13738207288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1380379918183237 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (12890582840 / 1000000000000) (12890582841 / 1000000000000), orderedInterval (40952060223 / 1000000000000) (40952060224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (446386503845221 / 800000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14240023890 / 1000000000000) (-14240023751 / 1000000000000), orderedInterval (30642029849 / 1000000000000) (30642029988 / 1000000000000)))) (orderedInterval (-14268082171 / 1000000000000) (-14268082129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (402791417409359 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64723846748 / 1000000000000) (64723846749 / 1000000000000), orderedInterval (45861714243 / 1000000000000) (45861714244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1081954404461123 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43160090012 / 1000000000000) (43160090013 / 1000000000000), orderedInterval (22074138200 / 1000000000000) (22074138201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2937716678217591 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2403210286 / 1000000000000) (2403210287 / 1000000000000), orderedInterval (29341972018 / 1000000000000) (29341972019 / 1000000000000)))) (orderedInterval (702799011 / 1000000000000) (702799068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2163908808923183 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33853279599 / 1000000000000) (33853279678 / 1000000000000), orderedInterval (5514061825 / 1000000000000) (5514061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3707894626734059 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21896044604 / 1000000000000) (-21896044601 / 1000000000000), orderedInterval (-14387336311 / 1000000000000) (-14387336308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2731218399935681 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29229608583 / 1000000000000) (-29229576611 / 1000000000000), orderedInterval (8852627527 / 1000000000000) (8852659499 / 1000000000000)))) (orderedInterval (-31060361 / 1000000000000) (-31059562 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks0_1 :
    compactCertificate597.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4190391389834063 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19444558435 / 1000000000000) (-19444556168 / 1000000000000), orderedInterval (15161968307 / 1000000000000) (15161970574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2419323596930327 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21179294539 / 1000000000000) (21179297592 / 1000000000000), orderedInterval (-24593834963 / 1000000000000) (-24593831910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4293132177826243 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8496541993 / 1000000000000) (-8496541992 / 1000000000000), orderedInterval (22828520087 / 1000000000000) (22828520089 / 1000000000000)))) (orderedInterval (3816440700 / 1000000000000) (3816441514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4011200970984367 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24900445247 / 1000000000000) (-24900443477 / 1000000000000), orderedInterval (-3835942855 / 1000000000000) (-3835941085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2862582284114911 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4388360500 / 1000000000000) (4388360501 / 1000000000000), orderedInterval (29498062955 / 1000000000000) (29498062956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3245863213383369 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27697676536 / 1000000000000) (27697691795 / 1000000000000), orderedInterval (-4184658676 / 1000000000000) (-4184643416 / 1000000000000)))) (orderedInterval (724339491 / 1000000000000) (724339656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2706062349067961 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29416372615 / 1000000000000) (-29416343175 / 1000000000000), orderedInterval (8722596807 / 1000000000000) (8722626247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2390888152039181 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32616835749 / 1000000000000) (32616837185 / 1000000000000), orderedInterval (-1131021004 / 1000000000000) (-1131019568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (692972575802919 / 800000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2128607281 / 1000000000000) (-2128607280 / 1000000000000), orderedInterval (27027379649 / 1000000000000) (27027379650 / 1000000000000)))) (orderedInterval (-2260744547 / 1000000000000) (-2260744080 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks0_2 :
    compactCertificate597.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1916798613819493 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22887059325 / 1000000000000) (22887063602 / 1000000000000), orderedInterval (-28390921487 / 1000000000000) (-28390917210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1624891412898173 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39005397578 / 1000000000000) (-39005395294 / 1000000000000), orderedInterval (6811639734 / 1000000000000) (6811642018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1016781600064319 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-24487378312 / 1000000000000) (-24487378311 / 1000000000000), orderedInterval (-43596091469 / 1000000000000) (-43596091468 / 1000000000000)))) (orderedInterval (-2248958128 / 1000000000000) (-2248957197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (546828526177473 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45936260463 / 1000000000000) (-45936219187 / 1000000000000), orderedInterval (50632620428 / 1000000000000) (50632661705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1484745821871419 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39474697912 / 1000000000000) (39474697914 / 1000000000000), orderedInterval (12470454041 / 1000000000000) (12470454043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2027293484940763 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34414583770 / 1000000000000) (-34414575540 / 1000000000000), orderedInterval (8503543108 / 1000000000000) (8503551337 / 1000000000000)))) (orderedInterval (2590154791 / 1000000000000) (2590156240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (857218399935681 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54175903410 / 1000000000000) (54175903424 / 1000000000000), orderedInterval (5839676922 / 1000000000000) (5839676937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3484545204396001 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26806488316 / 1000000000000) (-26806471434 / 1000000000000), orderedInterval (3508927324 / 1000000000000) (3508944205 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2327514708551759 / 4000000000000) 0 (IntervalRat.scale (937 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32906326907 / 1000000000000) (-32906326663 / 1000000000000), orderedInterval (-3325787026 / 1000000000000) (-3325786783 / 1000000000000)))) (orderedInterval (8682784248 / 1000000000000) (8682785798 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks0 :
    compactCertificate597.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate597.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate597_chunkChecks0_0
    compactCertificate597_chunkChecks0_1 compactCertificate597_chunkChecks0_2

theorem compactCertificate597_chunkChecks1_0 :
    compactCertificate597.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (937 / 2) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34192163241 / 1000000000000) (-34192163239 / 1000000000000), orderedInterval (-13738207290 / 1000000000000) (-13738207288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1380379918183237 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (12890582840 / 1000000000000) (12890582841 / 1000000000000), orderedInterval (40952060223 / 1000000000000) (40952060224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (446386503845221 / 800000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14240023890 / 1000000000000) (-14240023751 / 1000000000000), orderedInterval (30642029849 / 1000000000000) (30642029988 / 1000000000000)))) (orderedInterval (-3022717534 / 1000000000000) (-3022717487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (402791417409359 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64723846748 / 1000000000000) (64723846749 / 1000000000000), orderedInterval (45861714243 / 1000000000000) (45861714244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1081954404461123 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43160090012 / 1000000000000) (43160090013 / 1000000000000), orderedInterval (22074138200 / 1000000000000) (22074138201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2937716678217591 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2403210286 / 1000000000000) (2403210287 / 1000000000000), orderedInterval (29341972018 / 1000000000000) (29341972019 / 1000000000000)))) (orderedInterval (-2911532245 / 1000000000000) (-2911532181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2163908808923183 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33853279599 / 1000000000000) (33853279678 / 1000000000000), orderedInterval (5514061825 / 1000000000000) (5514061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3707894626734059 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21896044604 / 1000000000000) (-21896044601 / 1000000000000), orderedInterval (-14387336311 / 1000000000000) (-14387336308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2731218399935681 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29229608583 / 1000000000000) (-29229576611 / 1000000000000), orderedInterval (8852627527 / 1000000000000) (8852659499 / 1000000000000)))) (orderedInterval (1189846378 / 1000000000000) (1189847550 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks1_1 :
    compactCertificate597.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4190391389834063 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19444558435 / 1000000000000) (-19444556168 / 1000000000000), orderedInterval (15161968307 / 1000000000000) (15161970574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2419323596930327 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21179294539 / 1000000000000) (21179297592 / 1000000000000), orderedInterval (-24593834963 / 1000000000000) (-24593831910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4293132177826243 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8496541993 / 1000000000000) (-8496541992 / 1000000000000), orderedInterval (22828520087 / 1000000000000) (22828520089 / 1000000000000)))) (orderedInterval (-942216543 / 1000000000000) (-942214965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4011200970984367 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24900445247 / 1000000000000) (-24900443477 / 1000000000000), orderedInterval (-3835942855 / 1000000000000) (-3835941085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2862582284114911 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4388360500 / 1000000000000) (4388360501 / 1000000000000), orderedInterval (29498062955 / 1000000000000) (29498062956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3245863213383369 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27697676536 / 1000000000000) (27697691795 / 1000000000000), orderedInterval (-4184658676 / 1000000000000) (-4184643416 / 1000000000000)))) (orderedInterval (4445817922 / 1000000000000) (4445818215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2706062349067961 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29416372615 / 1000000000000) (-29416343175 / 1000000000000), orderedInterval (8722596807 / 1000000000000) (8722626247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2390888152039181 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32616835749 / 1000000000000) (32616837185 / 1000000000000), orderedInterval (-1131021004 / 1000000000000) (-1131019568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (692972575802919 / 800000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2128607281 / 1000000000000) (-2128607280 / 1000000000000), orderedInterval (27027379649 / 1000000000000) (27027379650 / 1000000000000)))) (orderedInterval (1507486987 / 1000000000000) (1507487648 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks1_2 :
    compactCertificate597.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1916798613819493 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22887059325 / 1000000000000) (22887063602 / 1000000000000), orderedInterval (-28390921487 / 1000000000000) (-28390917210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1624891412898173 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39005397578 / 1000000000000) (-39005395294 / 1000000000000), orderedInterval (6811639734 / 1000000000000) (6811642018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1016781600064319 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-24487378312 / 1000000000000) (-24487378311 / 1000000000000), orderedInterval (-43596091469 / 1000000000000) (-43596091468 / 1000000000000)))) (orderedInterval (3538812764 / 1000000000000) (3538813684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (546828526177473 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45936260463 / 1000000000000) (-45936219187 / 1000000000000), orderedInterval (50632620428 / 1000000000000) (50632661705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1484745821871419 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39474697912 / 1000000000000) (39474697914 / 1000000000000), orderedInterval (12470454041 / 1000000000000) (12470454043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2027293484940763 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34414583770 / 1000000000000) (-34414575540 / 1000000000000), orderedInterval (8503543108 / 1000000000000) (8503551337 / 1000000000000)))) (orderedInterval (-1201974789 / 1000000000000) (-1201973834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (857218399935681 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54175903410 / 1000000000000) (54175903424 / 1000000000000), orderedInterval (5839676922 / 1000000000000) (5839676937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3484545204396001 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26806488316 / 1000000000000) (-26806471434 / 1000000000000), orderedInterval (3508927324 / 1000000000000) (3508944205 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2327514708551759 / 4000000000000) 1 (IntervalRat.scale (937 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32906326907 / 1000000000000) (-32906326663 / 1000000000000), orderedInterval (-3325787026 / 1000000000000) (-3325786783 / 1000000000000)))) (orderedInterval (260007487 / 1000000000000) (260010281 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks1 :
    compactCertificate597.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate597.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate597_chunkChecks1_0
    compactCertificate597_chunkChecks1_1 compactCertificate597_chunkChecks1_2

theorem compactCertificate597_chunkChecks2_0 :
    compactCertificate597.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (937 / 2) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34192163241 / 1000000000000) (-34192163239 / 1000000000000), orderedInterval (-13738207290 / 1000000000000) (-13738207288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1380379918183237 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (12890582840 / 1000000000000) (12890582841 / 1000000000000), orderedInterval (40952060223 / 1000000000000) (40952060224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (446386503845221 / 800000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14240023890 / 1000000000000) (-14240023751 / 1000000000000), orderedInterval (30642029849 / 1000000000000) (30642029988 / 1000000000000)))) (orderedInterval (14679167856 / 1000000000000) (14679167911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (402791417409359 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64723846748 / 1000000000000) (64723846749 / 1000000000000), orderedInterval (45861714243 / 1000000000000) (45861714244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1081954404461123 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43160090012 / 1000000000000) (43160090013 / 1000000000000), orderedInterval (22074138200 / 1000000000000) (22074138201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2937716678217591 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2403210286 / 1000000000000) (2403210287 / 1000000000000), orderedInterval (29341972018 / 1000000000000) (29341972019 / 1000000000000)))) (orderedInterval (-66793327 / 1000000000000) (-66793238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2163908808923183 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33853279599 / 1000000000000) (33853279678 / 1000000000000), orderedInterval (5514061825 / 1000000000000) (5514061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3707894626734059 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21896044604 / 1000000000000) (-21896044601 / 1000000000000), orderedInterval (-14387336311 / 1000000000000) (-14387336308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2731218399935681 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29229608583 / 1000000000000) (-29229576611 / 1000000000000), orderedInterval (8852627527 / 1000000000000) (8852659499 / 1000000000000)))) (orderedInterval (-1145977162 / 1000000000000) (-1145975436 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks2_1 :
    compactCertificate597.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4190391389834063 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19444558435 / 1000000000000) (-19444556168 / 1000000000000), orderedInterval (15161968307 / 1000000000000) (15161970574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2419323596930327 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21179294539 / 1000000000000) (21179297592 / 1000000000000), orderedInterval (-24593834963 / 1000000000000) (-24593831910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4293132177826243 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8496541993 / 1000000000000) (-8496541992 / 1000000000000), orderedInterval (22828520087 / 1000000000000) (22828520089 / 1000000000000)))) (orderedInterval (-13549721595 / 1000000000000) (-13549718376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4011200970984367 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24900445247 / 1000000000000) (-24900443477 / 1000000000000), orderedInterval (-3835942855 / 1000000000000) (-3835941085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2862582284114911 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4388360500 / 1000000000000) (4388360501 / 1000000000000), orderedInterval (29498062955 / 1000000000000) (29498062956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3245863213383369 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27697676536 / 1000000000000) (27697691795 / 1000000000000), orderedInterval (-4184658676 / 1000000000000) (-4184643416 / 1000000000000)))) (orderedInterval (-2616798694 / 1000000000000) (-2616798165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2706062349067961 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29416372615 / 1000000000000) (-29416343175 / 1000000000000), orderedInterval (8722596807 / 1000000000000) (8722626247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2390888152039181 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32616835749 / 1000000000000) (32616837185 / 1000000000000), orderedInterval (-1131021004 / 1000000000000) (-1131019568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (692972575802919 / 800000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2128607281 / 1000000000000) (-2128607280 / 1000000000000), orderedInterval (27027379649 / 1000000000000) (27027379650 / 1000000000000)))) (orderedInterval (3929618972 / 1000000000000) (3929619913 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks2_2 :
    compactCertificate597.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1916798613819493 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22887059325 / 1000000000000) (22887063602 / 1000000000000), orderedInterval (-28390921487 / 1000000000000) (-28390917210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1624891412898173 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39005397578 / 1000000000000) (-39005395294 / 1000000000000), orderedInterval (6811639734 / 1000000000000) (6811642018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1016781600064319 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-24487378312 / 1000000000000) (-24487378311 / 1000000000000), orderedInterval (-43596091469 / 1000000000000) (-43596091468 / 1000000000000)))) (orderedInterval (2395876408 / 1000000000000) (2395877326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (546828526177473 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45936260463 / 1000000000000) (-45936219187 / 1000000000000), orderedInterval (50632620428 / 1000000000000) (50632661705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1484745821871419 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39474697912 / 1000000000000) (39474697914 / 1000000000000), orderedInterval (12470454041 / 1000000000000) (12470454043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2027293484940763 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34414583770 / 1000000000000) (-34414575540 / 1000000000000), orderedInterval (8503543108 / 1000000000000) (8503551337 / 1000000000000)))) (orderedInterval (-2594136740 / 1000000000000) (-2594135885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (857218399935681 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54175903410 / 1000000000000) (54175903424 / 1000000000000), orderedInterval (5839676922 / 1000000000000) (5839676937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3484545204396001 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26806488316 / 1000000000000) (-26806471434 / 1000000000000), orderedInterval (3508927324 / 1000000000000) (3508944205 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2327514708551759 / 4000000000000) 2 (IntervalRat.scale (937 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32906326907 / 1000000000000) (-32906326663 / 1000000000000), orderedInterval (-3325787026 / 1000000000000) (-3325786783 / 1000000000000)))) (orderedInterval (-17137326844 / 1000000000000) (-17137321747 / 1000000000000))) = true
  rfl'

theorem compactCertificate597_chunkChecks2 :
    compactCertificate597.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate597.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate597_chunkChecks2_0
    compactCertificate597_chunkChecks2_1 compactCertificate597_chunkChecks2_2

theorem compactCertificate597_chunkChecks3_0 :
    compactCertificate597.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (937 / 2) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34192163241 / 1000000000000) (-34192163239 / 1000000000000), orderedInterval (-13738207290 / 1000000000000) (-13738207288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1380379918183237 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (12890582840 / 1000000000000) (12890582841 / 1000000000000), orderedInterval (40952060223 / 1000000000000) (40952060224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (446386503845221 / 800000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14240023890 / 1000000000000) (-14240023751 / 1000000000000), orderedInterval (30642029849 / 1000000000000) (30642029988 / 1000000000000)))) (orderedInterval (2223752585 / 1000000000000) (2223752649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (402791417409359 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64723846748 / 1000000000000) (64723846749 / 1000000000000), orderedInterval (45861714243 / 1000000000000) (45861714244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1081954404461123 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43160090012 / 1000000000000) (43160090013 / 1000000000000), orderedInterval (22074138200 / 1000000000000) (22074138201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2937716678217591 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2403210286 / 1000000000000) (2403210287 / 1000000000000), orderedInterval (29341972018 / 1000000000000) (29341972019 / 1000000000000)))) (orderedInterval (7885529892 / 1000000000000) (7885530025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2163908808923183 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33853279599 / 1000000000000) (33853279678 / 1000000000000), orderedInterval (5514061825 / 1000000000000) (5514061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3707894626734059 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21896044604 / 1000000000000) (-21896044601 / 1000000000000), orderedInterval (-14387336311 / 1000000000000) (-14387336308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2731218399935681 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29229608583 / 1000000000000) (-29229576611 / 1000000000000), orderedInterval (8852627527 / 1000000000000) (8852659499 / 1000000000000)))) (orderedInterval (-4097236073 / 1000000000000) (-4097233529 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate597_chunkChecks3_1 :
    compactCertificate597.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4190391389834063 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19444558435 / 1000000000000) (-19444556168 / 1000000000000), orderedInterval (15161968307 / 1000000000000) (15161970574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2419323596930327 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21179294539 / 1000000000000) (21179297592 / 1000000000000), orderedInterval (-24593834963 / 1000000000000) (-24593831910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4293132177826243 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8496541993 / 1000000000000) (-8496541992 / 1000000000000), orderedInterval (22828520087 / 1000000000000) (22828520089 / 1000000000000)))) (orderedInterval (-4946641963 / 1000000000000) (-4946635157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4011200970984367 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24900445247 / 1000000000000) (-24900443477 / 1000000000000), orderedInterval (-3835942855 / 1000000000000) (-3835941085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2862582284114911 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4388360500 / 1000000000000) (4388360501 / 1000000000000), orderedInterval (29498062955 / 1000000000000) (29498062956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3245863213383369 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27697676536 / 1000000000000) (27697691795 / 1000000000000), orderedInterval (-4184658676 / 1000000000000) (-4184643416 / 1000000000000)))) (orderedInterval (-10725665900 / 1000000000000) (-10725664930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2706062349067961 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29416372615 / 1000000000000) (-29416343175 / 1000000000000), orderedInterval (8722596807 / 1000000000000) (8722626247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2390888152039181 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32616835749 / 1000000000000) (32616837185 / 1000000000000), orderedInterval (-1131021004 / 1000000000000) (-1131019568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (692972575802919 / 800000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2128607281 / 1000000000000) (-2128607280 / 1000000000000), orderedInterval (27027379649 / 1000000000000) (27027379650 / 1000000000000)))) (orderedInterval (-4819888656 / 1000000000000) (-4819887311 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate597_chunkChecks3_2 :
    compactCertificate597.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1916798613819493 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22887059325 / 1000000000000) (22887063602 / 1000000000000), orderedInterval (-28390921487 / 1000000000000) (-28390917210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1624891412898173 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39005397578 / 1000000000000) (-39005395294 / 1000000000000), orderedInterval (6811639734 / 1000000000000) (6811642018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1016781600064319 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-24487378312 / 1000000000000) (-24487378311 / 1000000000000), orderedInterval (-43596091469 / 1000000000000) (-43596091468 / 1000000000000)))) (orderedInterval (-4384750647 / 1000000000000) (-4384749728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (546828526177473 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45936260463 / 1000000000000) (-45936219187 / 1000000000000), orderedInterval (50632620428 / 1000000000000) (50632661705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1484745821871419 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39474697912 / 1000000000000) (39474697914 / 1000000000000), orderedInterval (12470454041 / 1000000000000) (12470454043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2027293484940763 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34414583770 / 1000000000000) (-34414575540 / 1000000000000), orderedInterval (8503543108 / 1000000000000) (8503551337 / 1000000000000)))) (orderedInterval (994532451 / 1000000000000) (994533322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (857218399935681 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54175903410 / 1000000000000) (54175903424 / 1000000000000), orderedInterval (5839676922 / 1000000000000) (5839676937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3484545204396001 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26806488316 / 1000000000000) (-26806471434 / 1000000000000), orderedInterval (3508927324 / 1000000000000) (3508944205 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2327514708551759 / 4000000000000) 3 (IntervalRat.scale (937 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32906326907 / 1000000000000) (-32906326663 / 1000000000000), orderedInterval (-3325787026 / 1000000000000) (-3325786783 / 1000000000000)))) (orderedInterval (673965058 / 1000000000000) (673974405 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate597_chunkChecks3 :
    compactCertificate597.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate597.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate597_chunkChecks3_0
    compactCertificate597_chunkChecks3_1 compactCertificate597_chunkChecks3_2

theorem compactCertificate597_chunkChecks4_0 :
    compactCertificate597.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (937 / 2) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34192163241 / 1000000000000) (-34192163239 / 1000000000000), orderedInterval (-13738207290 / 1000000000000) (-13738207288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1380379918183237 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (12890582840 / 1000000000000) (12890582841 / 1000000000000), orderedInterval (40952060223 / 1000000000000) (40952060224 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (446386503845221 / 800000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-14240023890 / 1000000000000) (-14240023751 / 1000000000000), orderedInterval (30642029849 / 1000000000000) (30642029988 / 1000000000000)))) (orderedInterval (-15207981062 / 1000000000000) (-15207980987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (402791417409359 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (64723846748 / 1000000000000) (64723846749 / 1000000000000), orderedInterval (45861714243 / 1000000000000) (45861714244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1081954404461123 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43160090012 / 1000000000000) (43160090013 / 1000000000000), orderedInterval (22074138200 / 1000000000000) (22074138201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2937716678217591 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2403210286 / 1000000000000) (2403210287 / 1000000000000), orderedInterval (29341972018 / 1000000000000) (29341972019 / 1000000000000)))) (orderedInterval (-891781610 / 1000000000000) (-891781405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2163908808923183 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33853279599 / 1000000000000) (33853279678 / 1000000000000), orderedInterval (5514061825 / 1000000000000) (5514061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3707894626734059 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21896044604 / 1000000000000) (-21896044601 / 1000000000000), orderedInterval (-14387336311 / 1000000000000) (-14387336308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2731218399935681 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29229608583 / 1000000000000) (-29229576611 / 1000000000000), orderedInterval (8852627527 / 1000000000000) (8852659499 / 1000000000000)))) (orderedInterval (7180917583 / 1000000000000) (7180921354 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate597_chunkChecks4_1 :
    compactCertificate597.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4190391389834063 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19444558435 / 1000000000000) (-19444556168 / 1000000000000), orderedInterval (15161968307 / 1000000000000) (15161970574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2419323596930327 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21179294539 / 1000000000000) (21179297592 / 1000000000000), orderedInterval (-24593834963 / 1000000000000) (-24593831910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4293132177826243 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-8496541993 / 1000000000000) (-8496541992 / 1000000000000), orderedInterval (22828520087 / 1000000000000) (22828520089 / 1000000000000)))) (orderedInterval (57488616273 / 1000000000000) (57488631011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4011200970984367 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24900445247 / 1000000000000) (-24900443477 / 1000000000000), orderedInterval (-3835942855 / 1000000000000) (-3835941085 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2862582284114911 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4388360500 / 1000000000000) (4388360501 / 1000000000000), orderedInterval (29498062955 / 1000000000000) (29498062956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3245863213383369 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27697676536 / 1000000000000) (27697691795 / 1000000000000), orderedInterval (-4184658676 / 1000000000000) (-4184643416 / 1000000000000)))) (orderedInterval (10479373546 / 1000000000000) (10479375356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2706062349067961 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29416372615 / 1000000000000) (-29416343175 / 1000000000000), orderedInterval (8722596807 / 1000000000000) (8722626247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2390888152039181 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32616835749 / 1000000000000) (32616837185 / 1000000000000), orderedInterval (-1131021004 / 1000000000000) (-1131019568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (692972575802919 / 800000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2128607281 / 1000000000000) (-2128607280 / 1000000000000), orderedInterval (27027379649 / 1000000000000) (27027379650 / 1000000000000)))) (orderedInterval (-7038593172 / 1000000000000) (-7038591235 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate597_chunkChecks4_2 :
    compactCertificate597.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1916798613819493 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22887059325 / 1000000000000) (22887063602 / 1000000000000), orderedInterval (-28390921487 / 1000000000000) (-28390917210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1624891412898173 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39005397578 / 1000000000000) (-39005395294 / 1000000000000), orderedInterval (6811639734 / 1000000000000) (6811642018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1016781600064319 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-24487378312 / 1000000000000) (-24487378311 / 1000000000000), orderedInterval (-43596091469 / 1000000000000) (-43596091468 / 1000000000000)))) (orderedInterval (-2807912677 / 1000000000000) (-2807911752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (546828526177473 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-45936260463 / 1000000000000) (-45936219187 / 1000000000000), orderedInterval (50632620428 / 1000000000000) (50632661705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1484745821871419 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39474697912 / 1000000000000) (39474697914 / 1000000000000), orderedInterval (12470454041 / 1000000000000) (12470454043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2027293484940763 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34414583770 / 1000000000000) (-34414575540 / 1000000000000), orderedInterval (8503543108 / 1000000000000) (8503551337 / 1000000000000)))) (orderedInterval (3261280473 / 1000000000000) (3261281400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (857218399935681 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54175903410 / 1000000000000) (54175903424 / 1000000000000), orderedInterval (5839676922 / 1000000000000) (5839676937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3484545204396001 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26806488316 / 1000000000000) (-26806471434 / 1000000000000), orderedInterval (3508927324 / 1000000000000) (3508944205 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2327514708551759 / 4000000000000) 4 (IntervalRat.scale (937 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32906326907 / 1000000000000) (-32906326663 / 1000000000000), orderedInterval (-3325787026 / 1000000000000) (-3325786783 / 1000000000000)))) (orderedInterval (40787130536 / 1000000000000) (40787147776 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate597_chunkChecks4 :
    compactCertificate597.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate597.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate597_chunkChecks4_0
    compactCertificate597_chunkChecks4_1 compactCertificate597_chunkChecks4_2

theorem compactCertificate597_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate597.chunkCheck r b = true :=
  compactCertificate597.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate597_chunkChecks0
    · exact compactCertificate597_chunkChecks1
    · exact compactCertificate597_chunkChecks2
    · exact compactCertificate597_chunkChecks3
    · exact compactCertificate597_chunkChecks4)

theorem compactCertificate597_coefficient0 :
    compactCertificate597.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate597_coefficient1 :
    compactCertificate597.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate597_coefficient2 :
    compactCertificate597.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate597_coefficient3 :
    compactCertificate597.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate597_coefficient4 :
    compactCertificate597.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate597_coefficients : ∀ r : Fin 5,
    compactCertificate597.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate597_coefficient0
  · exact compactCertificate597_coefficient1
  · exact compactCertificate597_coefficient2
  · exact compactCertificate597_coefficient3
  · exact compactCertificate597_coefficient4

theorem compactCertificate597_lower : (1 : ℚ) ≤ compactCertificate597.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate597, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate597_proves {t : ℝ} (ht : t ∈ compactCertificate597.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate597.proves compactCertificate597_states compactCertificate597_chunks
    compactCertificate597_coefficients compactCertificate597_lower ht

end Erdos232
