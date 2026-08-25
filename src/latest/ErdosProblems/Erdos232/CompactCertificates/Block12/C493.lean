/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate493 : CompactCertificate where
  left := 364
  right := 365
  center := 729 / 2
  grid := fun i =>
    match i.val with
    | 0 => 116
    | 1 => 86
    | 2 => 138
    | 3 => 25
    | 4 => 67
    | 5 => 182
    | 6 => 134
    | 7 => 230
    | 8 => 169
    | 9 => 260
    | 10 => 150
    | 11 => 266
    | 12 => 248
    | 13 => 177
    | 14 => 201
    | 15 => 168
    | 16 => 148
    | 17 => 215
    | 18 => 119
    | 19 => 101
    | 20 => 63
    | 21 => 34
    | 22 => 92
    | 23 => 126
    | 24 => 53
    | 25 => 216
    | _ => 144
  point := fun i =>
    match i.val with
    | 0 => 729 / 2
    | 1 => 1073956201019829 / 4000000000000
    | 2 => 347295369587157 / 800000000000
    | 3 => 313377740972703 / 4000000000000
    | 4 => 841776692478291 / 4000000000000
    | 5 => 2285587468965447 / 4000000000000
    | 6 => 1683553384957311 / 4000000000000
    | 7 => 2884797420372603 / 4000000000000
    | 8 => 2124928723108977 / 4000000000000
    | 9 => 3260187111194271 / 4000000000000
    | 10 => 1882269906256359 / 4000000000000
    | 11 => 3340120979333331 / 4000000000000
    | 12 => 3120774287991039 / 4000000000000
    | 13 => 2227131787747887 / 4000000000000
    | 14 => 2525330077434873 / 4000000000000
    | 15 => 2105356939669737 / 4000000000000
    | 16 => 1860146705268477 / 4000000000000
    | 17 => 539143017887223 / 800000000000
    | 18 => 1491297961018581 / 4000000000000
    | 19 => 1264189797228141 / 4000000000000
    | 20 => 791071276891023 / 4000000000000
    | 21 => 425440763696241 / 4000000000000
    | 22 => 1155154433451723 / 4000000000000
    | 23 => 1577264621688171 / 4000000000000
    | 24 => 666928723108977 / 4000000000000
    | 25 => 2711028232662417 / 4000000000000
    | _ => 1810841219353503 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (31679986424 / 1000000000000) (31679986425 / 1000000000000), orderedInterval (27213368467 / 1000000000000) (27213368468 / 1000000000000))
    | 1 => (orderedInterval (-38233642586 / 1000000000000) (-38233546087 / 1000000000000), orderedInterval (30225939232 / 1000000000000) (30226035731 / 1000000000000))
    | 2 => (orderedInterval (37482710955 / 1000000000000) (37482710974 / 1000000000000), orderedInterval (7799565293 / 1000000000000) (7799565312 / 1000000000000))
    | 3 => (orderedInterval (-50033716690 / 1000000000000) (-50033716689 / 1000000000000), orderedInterval (-74664692181 / 1000000000000) (-74664692180 / 1000000000000))
    | 4 => (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))
    | 5 => (orderedInterval (13371927433 / 1000000000000) (13371927434 / 1000000000000), orderedInterval (30571599324 / 1000000000000) (30571599325 / 1000000000000))
    | 6 => (orderedInterval (25055640805 / 1000000000000) (25055640806 / 1000000000000), orderedInterval (29715439048 / 1000000000000) (29715439049 / 1000000000000))
    | 7 => (orderedInterval (-16325133748 / 1000000000000) (-16325133424 / 1000000000000), orderedInterval (24834972120 / 1000000000000) (24834972445 / 1000000000000))
    | 8 => (orderedInterval (-30663847914 / 1000000000000) (-30663847913 / 1000000000000), orderedInterval (-16036985540 / 1000000000000) (-16036985539 / 1000000000000))
    | 9 => (orderedInterval (-23242776431 / 1000000000000) (-23242760041 / 1000000000000), orderedInterval (15533830889 / 1000000000000) (15533847279 / 1000000000000))
    | 10 => (orderedInterval (4173451232 / 1000000000000) (4173451233 / 1000000000000), orderedInterval (36539508156 / 1000000000000) (36539508157 / 1000000000000))
    | 11 => (orderedInterval (4176631511 / 1000000000000) (4176631512 / 1000000000000), orderedInterval (27291219158 / 1000000000000) (27291219159 / 1000000000000))
    | 12 => (orderedInterval (27347579884 / 1000000000000) (27347629496 / 1000000000000), orderedInterval (-8268916531 / 1000000000000) (-8268866919 / 1000000000000))
    | 13 => (orderedInterval (-33743558705 / 1000000000000) (-33743558370 / 1000000000000), orderedInterval (-2151736996 / 1000000000000) (-2151736661 / 1000000000000))
    | 14 => (orderedInterval (-19409112350 / 1000000000000) (-19409112349 / 1000000000000), orderedInterval (-25117499160 / 1000000000000) (-25117499159 / 1000000000000))
    | 15 => (orderedInterval (-21410094075 / 1000000000000) (-21410091289 / 1000000000000), orderedInterval (27427120155 / 1000000000000) (27427122941 / 1000000000000))
    | 16 => (orderedInterval (28186388584 / 1000000000000) (28186388585 / 1000000000000), orderedInterval (23938302597 / 1000000000000) (23938302598 / 1000000000000))
    | 17 => (orderedInterval (20460369619 / 1000000000000) (20460372126 / 1000000000000), orderedInterval (-22950150130 / 1000000000000) (-22950147623 / 1000000000000))
    | 18 => (orderedInterval (9821392438 / 1000000000000) (9821392470 / 1000000000000), orderedInterval (-40151688027 / 1000000000000) (-40151687995 / 1000000000000))
    | 19 => (orderedInterval (20262234244 / 1000000000000) (20262235260 / 1000000000000), orderedInterval (-40079033592 / 1000000000000) (-40079032576 / 1000000000000))
    | 20 => (orderedInterval (-33528917181 / 1000000000000) (-33528917180 / 1000000000000), orderedInterval (-45684664288 / 1000000000000) (-45684664287 / 1000000000000))
    | 21 => (orderedInterval (25089092735 / 1000000000000) (25089092736 / 1000000000000), orderedInterval (73067423493 / 1000000000000) (73067423494 / 1000000000000))
    | 22 => (orderedInterval (24422757711 / 1000000000000) (24422757712 / 1000000000000), orderedInterval (40057334595 / 1000000000000) (40057334596 / 1000000000000))
    | 23 => (orderedInterval (-27076685798 / 1000000000000) (-27076673477 / 1000000000000), orderedInterval (29721769913 / 1000000000000) (29721782235 / 1000000000000))
    | 24 => (orderedInterval (-52406419370 / 1000000000000) (-52406419369 / 1000000000000), orderedInterval (-32580855946 / 1000000000000) (-32580855945 / 1000000000000))
    | 25 => (orderedInterval (-1278917702 / 1000000000000) (-1278917701 / 1000000000000), orderedInterval (30622315320 / 1000000000000) (30622315321 / 1000000000000))
    | _ => (orderedInterval (33523039739 / 1000000000000) (33523039740 / 1000000000000), orderedInterval (16769112509 / 1000000000000) (16769112510 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14400102418 / 1000000000000) (14400103344 / 1000000000000)
      | 1 => orderedInterval (-1765231844 / 1000000000000) (-1765231799 / 1000000000000)
      | 2 => orderedInterval (-237552283 / 1000000000000) (-237552252 / 1000000000000)
      | 3 => orderedInterval (5032908925 / 1000000000000) (5032911982 / 1000000000000)
      | 4 => orderedInterval (-3586375461 / 1000000000000) (-3586374490 / 1000000000000)
      | 5 => orderedInterval (-1336383793 / 1000000000000) (-1336383662 / 1000000000000)
      | 6 => orderedInterval (-3808751081 / 1000000000000) (-3808750927 / 1000000000000)
      | 7 => orderedInterval (1057776870 / 1000000000000) (1057777858 / 1000000000000)
      | _ => orderedInterval (-6501628483 / 1000000000000) (-6501628382 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11538991889 / 1000000000000) (11538992582 / 1000000000000)
      | 1 => orderedInterval (-4085394471 / 1000000000000) (-4085394421 / 1000000000000)
      | 2 => orderedInterval (-2080499461 / 1000000000000) (-2080499405 / 1000000000000)
      | 3 => orderedInterval (6210898824 / 1000000000000) (6210905636 / 1000000000000)
      | 4 => orderedInterval (228870048 / 1000000000000) (228872084 / 1000000000000)
      | 5 => orderedInterval (-2376863320 / 1000000000000) (-2376863103 / 1000000000000)
      | 6 => orderedInterval (7726541233 / 1000000000000) (7726541373 / 1000000000000)
      | 7 => orderedInterval (-3577875345 / 1000000000000) (-3577874284 / 1000000000000)
      | _ => orderedInterval (-8632581995 / 1000000000000) (-8632581853 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15515181131 / 1000000000000) (-15515180606 / 1000000000000)
      | 1 => orderedInterval (2774659942 / 1000000000000) (2774660011 / 1000000000000)
      | 2 => orderedInterval (-391414910 / 1000000000000) (-391414807 / 1000000000000)
      | 3 => orderedInterval (-24298228497 / 1000000000000) (-24298213275 / 1000000000000)
      | 4 => orderedInterval (9412047024 / 1000000000000) (9412051324 / 1000000000000)
      | 5 => orderedInterval (1356751150 / 1000000000000) (1356751513 / 1000000000000)
      | 6 => orderedInterval (2805260227 / 1000000000000) (2805260357 / 1000000000000)
      | 7 => orderedInterval (-2031437914 / 1000000000000) (-2031436766 / 1000000000000)
      | _ => orderedInterval (9432340097 / 1000000000000) (9432340307 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11629557147 / 1000000000000) (-11629556746 / 1000000000000)
      | 1 => orderedInterval (8640814017 / 1000000000000) (8640814121 / 1000000000000)
      | 2 => orderedInterval (7134357926 / 1000000000000) (7134358120 / 1000000000000)
      | 3 => orderedInterval (-21543387080 / 1000000000000) (-21543353071 / 1000000000000)
      | 4 => orderedInterval (-1424980028 / 1000000000000) (-1424970922 / 1000000000000)
      | 5 => orderedInterval (5601490851 / 1000000000000) (5601491471 / 1000000000000)
      | 6 => orderedInterval (-8118773844 / 1000000000000) (-8118773723 / 1000000000000)
      | 7 => orderedInterval (3374830019 / 1000000000000) (3374831258 / 1000000000000)
      | _ => orderedInterval (22045976878 / 1000000000000) (22045977202 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16941286188 / 1000000000000) (16941286502 / 1000000000000)
      | 1 => orderedInterval (-5937718273 / 1000000000000) (-5937718113 / 1000000000000)
      | 2 => orderedInterval (4334424130 / 1000000000000) (4334424497 / 1000000000000)
      | 3 => orderedInterval (120579371235 / 1000000000000) (120579447347 / 1000000000000)
      | 4 => orderedInterval (-26843848205 / 1000000000000) (-26843828840 / 1000000000000)
      | 5 => orderedInterval (742604758 / 1000000000000) (742605834 / 1000000000000)
      | 6 => orderedInterval (-2417060686 / 1000000000000) (-2417060570 / 1000000000000)
      | 7 => orderedInterval (2601841151 / 1000000000000) (2601842493 / 1000000000000)
      | _ => orderedInterval (-13857063853 / 1000000000000) (-13857063333 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (3254865268 / 1000000000000) (3254871672 / 1000000000000)
    | 1 => orderedInterval (4952087402 / 1000000000000) (4952098609 / 1000000000000)
    | 2 => orderedInterval (-16455204012 / 1000000000000) (-16455181942 / 1000000000000)
    | 3 => orderedInterval (4080771592 / 1000000000000) (4080817710 / 1000000000000)
    | _ => orderedInterval (96143836445 / 1000000000000) (96143935817 / 1000000000000)

theorem compactCertificate493_stateChecks0 :
    compactCertificate493.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (729 / 2)) (orderedInterval (31679986424 / 1000000000000) (31679986425 / 1000000000000), orderedInterval (27213368467 / 1000000000000) (27213368468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1073956201019829 / 4000000000000)) (orderedInterval (-38233642586 / 1000000000000) (-38233546087 / 1000000000000), orderedInterval (30225939232 / 1000000000000) (30226035731 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (347295369587157 / 800000000000)) (orderedInterval (37482710955 / 1000000000000) (37482710974 / 1000000000000), orderedInterval (7799565293 / 1000000000000) (7799565312 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks1 :
    compactCertificate493.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (313377740972703 / 4000000000000)) (orderedInterval (-50033716690 / 1000000000000) (-50033716689 / 1000000000000), orderedInterval (-74664692181 / 1000000000000) (-74664692180 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (841776692478291 / 4000000000000)) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2285587468965447 / 4000000000000)) (orderedInterval (13371927433 / 1000000000000) (13371927434 / 1000000000000), orderedInterval (30571599324 / 1000000000000) (30571599325 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks2 :
    compactCertificate493.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1683553384957311 / 4000000000000)) (orderedInterval (25055640805 / 1000000000000) (25055640806 / 1000000000000), orderedInterval (29715439048 / 1000000000000) (29715439049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2884797420372603 / 4000000000000)) (orderedInterval (-16325133748 / 1000000000000) (-16325133424 / 1000000000000), orderedInterval (24834972120 / 1000000000000) (24834972445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2124928723108977 / 4000000000000)) (orderedInterval (-30663847914 / 1000000000000) (-30663847913 / 1000000000000), orderedInterval (-16036985540 / 1000000000000) (-16036985539 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks3 :
    compactCertificate493.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3260187111194271 / 4000000000000)) (orderedInterval (-23242776431 / 1000000000000) (-23242760041 / 1000000000000), orderedInterval (15533830889 / 1000000000000) (15533847279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1882269906256359 / 4000000000000)) (orderedInterval (4173451232 / 1000000000000) (4173451233 / 1000000000000), orderedInterval (36539508156 / 1000000000000) (36539508157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3340120979333331 / 4000000000000)) (orderedInterval (4176631511 / 1000000000000) (4176631512 / 1000000000000), orderedInterval (27291219158 / 1000000000000) (27291219159 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks4 :
    compactCertificate493.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3120774287991039 / 4000000000000)) (orderedInterval (27347579884 / 1000000000000) (27347629496 / 1000000000000), orderedInterval (-8268916531 / 1000000000000) (-8268866919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2227131787747887 / 4000000000000)) (orderedInterval (-33743558705 / 1000000000000) (-33743558370 / 1000000000000), orderedInterval (-2151736996 / 1000000000000) (-2151736661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2525330077434873 / 4000000000000)) (orderedInterval (-19409112350 / 1000000000000) (-19409112349 / 1000000000000), orderedInterval (-25117499160 / 1000000000000) (-25117499159 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks5 :
    compactCertificate493.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2105356939669737 / 4000000000000)) (orderedInterval (-21410094075 / 1000000000000) (-21410091289 / 1000000000000), orderedInterval (27427120155 / 1000000000000) (27427122941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1860146705268477 / 4000000000000)) (orderedInterval (28186388584 / 1000000000000) (28186388585 / 1000000000000), orderedInterval (23938302597 / 1000000000000) (23938302598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (539143017887223 / 800000000000)) (orderedInterval (20460369619 / 1000000000000) (20460372126 / 1000000000000), orderedInterval (-22950150130 / 1000000000000) (-22950147623 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks6 :
    compactCertificate493.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1491297961018581 / 4000000000000)) (orderedInterval (9821392438 / 1000000000000) (9821392470 / 1000000000000), orderedInterval (-40151688027 / 1000000000000) (-40151687995 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1264189797228141 / 4000000000000)) (orderedInterval (20262234244 / 1000000000000) (20262235260 / 1000000000000), orderedInterval (-40079033592 / 1000000000000) (-40079032576 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (791071276891023 / 4000000000000)) (orderedInterval (-33528917181 / 1000000000000) (-33528917180 / 1000000000000), orderedInterval (-45684664288 / 1000000000000) (-45684664287 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks7 :
    compactCertificate493.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (425440763696241 / 4000000000000)) (orderedInterval (25089092735 / 1000000000000) (25089092736 / 1000000000000), orderedInterval (73067423493 / 1000000000000) (73067423494 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1155154433451723 / 4000000000000)) (orderedInterval (24422757711 / 1000000000000) (24422757712 / 1000000000000), orderedInterval (40057334595 / 1000000000000) (40057334596 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1577264621688171 / 4000000000000)) (orderedInterval (-27076685798 / 1000000000000) (-27076673477 / 1000000000000), orderedInterval (29721769913 / 1000000000000) (29721782235 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_stateChecks8 :
    compactCertificate493.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (666928723108977 / 4000000000000)) (orderedInterval (-52406419370 / 1000000000000) (-52406419369 / 1000000000000), orderedInterval (-32580855946 / 1000000000000) (-32580855945 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2711028232662417 / 4000000000000)) (orderedInterval (-1278917702 / 1000000000000) (-1278917701 / 1000000000000), orderedInterval (30622315320 / 1000000000000) (30622315321 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1810841219353503 / 4000000000000)) (orderedInterval (33523039739 / 1000000000000) (33523039740 / 1000000000000), orderedInterval (16769112509 / 1000000000000) (16769112510 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_states : ∀ j,
    BesselStateValid (compactCertificate493.point j) (compactCertificate493.state j) :=
  compactCertificate493.statesValid_of_checks3 compactCertificate493_stateChecks0
    compactCertificate493_stateChecks1 compactCertificate493_stateChecks2
    compactCertificate493_stateChecks3 compactCertificate493_stateChecks4
    compactCertificate493_stateChecks5 compactCertificate493_stateChecks6
    compactCertificate493_stateChecks7 compactCertificate493_stateChecks8

theorem compactCertificate493_chunkChecks0_0 :
    compactCertificate493.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (729 / 2) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31679986424 / 1000000000000) (31679986425 / 1000000000000), orderedInterval (27213368467 / 1000000000000) (27213368468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1073956201019829 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38233642586 / 1000000000000) (-38233546087 / 1000000000000), orderedInterval (30225939232 / 1000000000000) (30226035731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (347295369587157 / 800000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37482710955 / 1000000000000) (37482710974 / 1000000000000), orderedInterval (7799565293 / 1000000000000) (7799565312 / 1000000000000)))) (orderedInterval (14400102418 / 1000000000000) (14400103344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (313377740972703 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50033716690 / 1000000000000) (-50033716689 / 1000000000000), orderedInterval (-74664692181 / 1000000000000) (-74664692180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2285587468965447 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13371927433 / 1000000000000) (13371927434 / 1000000000000), orderedInterval (30571599324 / 1000000000000) (30571599325 / 1000000000000)))) (orderedInterval (-1765231844 / 1000000000000) (-1765231799 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1683553384957311 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25055640805 / 1000000000000) (25055640806 / 1000000000000), orderedInterval (29715439048 / 1000000000000) (29715439049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2884797420372603 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16325133748 / 1000000000000) (-16325133424 / 1000000000000), orderedInterval (24834972120 / 1000000000000) (24834972445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2124928723108977 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30663847914 / 1000000000000) (-30663847913 / 1000000000000), orderedInterval (-16036985540 / 1000000000000) (-16036985539 / 1000000000000)))) (orderedInterval (-237552283 / 1000000000000) (-237552252 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks0_1 :
    compactCertificate493.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3260187111194271 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23242776431 / 1000000000000) (-23242760041 / 1000000000000), orderedInterval (15533830889 / 1000000000000) (15533847279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1882269906256359 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4173451232 / 1000000000000) (4173451233 / 1000000000000), orderedInterval (36539508156 / 1000000000000) (36539508157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3340120979333331 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4176631511 / 1000000000000) (4176631512 / 1000000000000), orderedInterval (27291219158 / 1000000000000) (27291219159 / 1000000000000)))) (orderedInterval (5032908925 / 1000000000000) (5032911982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3120774287991039 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27347579884 / 1000000000000) (27347629496 / 1000000000000), orderedInterval (-8268916531 / 1000000000000) (-8268866919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2227131787747887 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33743558705 / 1000000000000) (-33743558370 / 1000000000000), orderedInterval (-2151736996 / 1000000000000) (-2151736661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2525330077434873 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19409112350 / 1000000000000) (-19409112349 / 1000000000000), orderedInterval (-25117499160 / 1000000000000) (-25117499159 / 1000000000000)))) (orderedInterval (-3586375461 / 1000000000000) (-3586374490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2105356939669737 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21410094075 / 1000000000000) (-21410091289 / 1000000000000), orderedInterval (27427120155 / 1000000000000) (27427122941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1860146705268477 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28186388584 / 1000000000000) (28186388585 / 1000000000000), orderedInterval (23938302597 / 1000000000000) (23938302598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (539143017887223 / 800000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20460369619 / 1000000000000) (20460372126 / 1000000000000), orderedInterval (-22950150130 / 1000000000000) (-22950147623 / 1000000000000)))) (orderedInterval (-1336383793 / 1000000000000) (-1336383662 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks0_2 :
    compactCertificate493.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1491297961018581 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9821392438 / 1000000000000) (9821392470 / 1000000000000), orderedInterval (-40151688027 / 1000000000000) (-40151687995 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1264189797228141 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20262234244 / 1000000000000) (20262235260 / 1000000000000), orderedInterval (-40079033592 / 1000000000000) (-40079032576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (791071276891023 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33528917181 / 1000000000000) (-33528917180 / 1000000000000), orderedInterval (-45684664288 / 1000000000000) (-45684664287 / 1000000000000)))) (orderedInterval (-3808751081 / 1000000000000) (-3808750927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (425440763696241 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25089092735 / 1000000000000) (25089092736 / 1000000000000), orderedInterval (73067423493 / 1000000000000) (73067423494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1155154433451723 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24422757711 / 1000000000000) (24422757712 / 1000000000000), orderedInterval (40057334595 / 1000000000000) (40057334596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1577264621688171 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27076685798 / 1000000000000) (-27076673477 / 1000000000000), orderedInterval (29721769913 / 1000000000000) (29721782235 / 1000000000000)))) (orderedInterval (1057776870 / 1000000000000) (1057777858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (666928723108977 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52406419370 / 1000000000000) (-52406419369 / 1000000000000), orderedInterval (-32580855946 / 1000000000000) (-32580855945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2711028232662417 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1278917702 / 1000000000000) (-1278917701 / 1000000000000), orderedInterval (30622315320 / 1000000000000) (30622315321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1810841219353503 / 4000000000000) 0 (IntervalRat.scale (729 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33523039739 / 1000000000000) (33523039740 / 1000000000000), orderedInterval (16769112509 / 1000000000000) (16769112510 / 1000000000000)))) (orderedInterval (-6501628483 / 1000000000000) (-6501628382 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks0 :
    compactCertificate493.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate493.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate493_chunkChecks0_0
    compactCertificate493_chunkChecks0_1 compactCertificate493_chunkChecks0_2

theorem compactCertificate493_chunkChecks1_0 :
    compactCertificate493.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (729 / 2) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31679986424 / 1000000000000) (31679986425 / 1000000000000), orderedInterval (27213368467 / 1000000000000) (27213368468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1073956201019829 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38233642586 / 1000000000000) (-38233546087 / 1000000000000), orderedInterval (30225939232 / 1000000000000) (30226035731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (347295369587157 / 800000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37482710955 / 1000000000000) (37482710974 / 1000000000000), orderedInterval (7799565293 / 1000000000000) (7799565312 / 1000000000000)))) (orderedInterval (11538991889 / 1000000000000) (11538992582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (313377740972703 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50033716690 / 1000000000000) (-50033716689 / 1000000000000), orderedInterval (-74664692181 / 1000000000000) (-74664692180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2285587468965447 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13371927433 / 1000000000000) (13371927434 / 1000000000000), orderedInterval (30571599324 / 1000000000000) (30571599325 / 1000000000000)))) (orderedInterval (-4085394471 / 1000000000000) (-4085394421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1683553384957311 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25055640805 / 1000000000000) (25055640806 / 1000000000000), orderedInterval (29715439048 / 1000000000000) (29715439049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2884797420372603 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16325133748 / 1000000000000) (-16325133424 / 1000000000000), orderedInterval (24834972120 / 1000000000000) (24834972445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2124928723108977 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30663847914 / 1000000000000) (-30663847913 / 1000000000000), orderedInterval (-16036985540 / 1000000000000) (-16036985539 / 1000000000000)))) (orderedInterval (-2080499461 / 1000000000000) (-2080499405 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks1_1 :
    compactCertificate493.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3260187111194271 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23242776431 / 1000000000000) (-23242760041 / 1000000000000), orderedInterval (15533830889 / 1000000000000) (15533847279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1882269906256359 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4173451232 / 1000000000000) (4173451233 / 1000000000000), orderedInterval (36539508156 / 1000000000000) (36539508157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3340120979333331 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4176631511 / 1000000000000) (4176631512 / 1000000000000), orderedInterval (27291219158 / 1000000000000) (27291219159 / 1000000000000)))) (orderedInterval (6210898824 / 1000000000000) (6210905636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3120774287991039 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27347579884 / 1000000000000) (27347629496 / 1000000000000), orderedInterval (-8268916531 / 1000000000000) (-8268866919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2227131787747887 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33743558705 / 1000000000000) (-33743558370 / 1000000000000), orderedInterval (-2151736996 / 1000000000000) (-2151736661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2525330077434873 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19409112350 / 1000000000000) (-19409112349 / 1000000000000), orderedInterval (-25117499160 / 1000000000000) (-25117499159 / 1000000000000)))) (orderedInterval (228870048 / 1000000000000) (228872084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2105356939669737 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21410094075 / 1000000000000) (-21410091289 / 1000000000000), orderedInterval (27427120155 / 1000000000000) (27427122941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1860146705268477 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28186388584 / 1000000000000) (28186388585 / 1000000000000), orderedInterval (23938302597 / 1000000000000) (23938302598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (539143017887223 / 800000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20460369619 / 1000000000000) (20460372126 / 1000000000000), orderedInterval (-22950150130 / 1000000000000) (-22950147623 / 1000000000000)))) (orderedInterval (-2376863320 / 1000000000000) (-2376863103 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks1_2 :
    compactCertificate493.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1491297961018581 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9821392438 / 1000000000000) (9821392470 / 1000000000000), orderedInterval (-40151688027 / 1000000000000) (-40151687995 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1264189797228141 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20262234244 / 1000000000000) (20262235260 / 1000000000000), orderedInterval (-40079033592 / 1000000000000) (-40079032576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (791071276891023 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33528917181 / 1000000000000) (-33528917180 / 1000000000000), orderedInterval (-45684664288 / 1000000000000) (-45684664287 / 1000000000000)))) (orderedInterval (7726541233 / 1000000000000) (7726541373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (425440763696241 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25089092735 / 1000000000000) (25089092736 / 1000000000000), orderedInterval (73067423493 / 1000000000000) (73067423494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1155154433451723 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24422757711 / 1000000000000) (24422757712 / 1000000000000), orderedInterval (40057334595 / 1000000000000) (40057334596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1577264621688171 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27076685798 / 1000000000000) (-27076673477 / 1000000000000), orderedInterval (29721769913 / 1000000000000) (29721782235 / 1000000000000)))) (orderedInterval (-3577875345 / 1000000000000) (-3577874284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (666928723108977 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52406419370 / 1000000000000) (-52406419369 / 1000000000000), orderedInterval (-32580855946 / 1000000000000) (-32580855945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2711028232662417 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1278917702 / 1000000000000) (-1278917701 / 1000000000000), orderedInterval (30622315320 / 1000000000000) (30622315321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1810841219353503 / 4000000000000) 1 (IntervalRat.scale (729 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33523039739 / 1000000000000) (33523039740 / 1000000000000), orderedInterval (16769112509 / 1000000000000) (16769112510 / 1000000000000)))) (orderedInterval (-8632581995 / 1000000000000) (-8632581853 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks1 :
    compactCertificate493.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate493.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate493_chunkChecks1_0
    compactCertificate493_chunkChecks1_1 compactCertificate493_chunkChecks1_2

theorem compactCertificate493_chunkChecks2_0 :
    compactCertificate493.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (729 / 2) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31679986424 / 1000000000000) (31679986425 / 1000000000000), orderedInterval (27213368467 / 1000000000000) (27213368468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1073956201019829 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38233642586 / 1000000000000) (-38233546087 / 1000000000000), orderedInterval (30225939232 / 1000000000000) (30226035731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (347295369587157 / 800000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37482710955 / 1000000000000) (37482710974 / 1000000000000), orderedInterval (7799565293 / 1000000000000) (7799565312 / 1000000000000)))) (orderedInterval (-15515181131 / 1000000000000) (-15515180606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (313377740972703 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50033716690 / 1000000000000) (-50033716689 / 1000000000000), orderedInterval (-74664692181 / 1000000000000) (-74664692180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2285587468965447 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13371927433 / 1000000000000) (13371927434 / 1000000000000), orderedInterval (30571599324 / 1000000000000) (30571599325 / 1000000000000)))) (orderedInterval (2774659942 / 1000000000000) (2774660011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1683553384957311 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25055640805 / 1000000000000) (25055640806 / 1000000000000), orderedInterval (29715439048 / 1000000000000) (29715439049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2884797420372603 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16325133748 / 1000000000000) (-16325133424 / 1000000000000), orderedInterval (24834972120 / 1000000000000) (24834972445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2124928723108977 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30663847914 / 1000000000000) (-30663847913 / 1000000000000), orderedInterval (-16036985540 / 1000000000000) (-16036985539 / 1000000000000)))) (orderedInterval (-391414910 / 1000000000000) (-391414807 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks2_1 :
    compactCertificate493.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3260187111194271 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23242776431 / 1000000000000) (-23242760041 / 1000000000000), orderedInterval (15533830889 / 1000000000000) (15533847279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1882269906256359 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4173451232 / 1000000000000) (4173451233 / 1000000000000), orderedInterval (36539508156 / 1000000000000) (36539508157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3340120979333331 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4176631511 / 1000000000000) (4176631512 / 1000000000000), orderedInterval (27291219158 / 1000000000000) (27291219159 / 1000000000000)))) (orderedInterval (-24298228497 / 1000000000000) (-24298213275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3120774287991039 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27347579884 / 1000000000000) (27347629496 / 1000000000000), orderedInterval (-8268916531 / 1000000000000) (-8268866919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2227131787747887 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33743558705 / 1000000000000) (-33743558370 / 1000000000000), orderedInterval (-2151736996 / 1000000000000) (-2151736661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2525330077434873 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19409112350 / 1000000000000) (-19409112349 / 1000000000000), orderedInterval (-25117499160 / 1000000000000) (-25117499159 / 1000000000000)))) (orderedInterval (9412047024 / 1000000000000) (9412051324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2105356939669737 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21410094075 / 1000000000000) (-21410091289 / 1000000000000), orderedInterval (27427120155 / 1000000000000) (27427122941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1860146705268477 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28186388584 / 1000000000000) (28186388585 / 1000000000000), orderedInterval (23938302597 / 1000000000000) (23938302598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (539143017887223 / 800000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20460369619 / 1000000000000) (20460372126 / 1000000000000), orderedInterval (-22950150130 / 1000000000000) (-22950147623 / 1000000000000)))) (orderedInterval (1356751150 / 1000000000000) (1356751513 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks2_2 :
    compactCertificate493.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1491297961018581 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9821392438 / 1000000000000) (9821392470 / 1000000000000), orderedInterval (-40151688027 / 1000000000000) (-40151687995 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1264189797228141 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20262234244 / 1000000000000) (20262235260 / 1000000000000), orderedInterval (-40079033592 / 1000000000000) (-40079032576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (791071276891023 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33528917181 / 1000000000000) (-33528917180 / 1000000000000), orderedInterval (-45684664288 / 1000000000000) (-45684664287 / 1000000000000)))) (orderedInterval (2805260227 / 1000000000000) (2805260357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (425440763696241 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25089092735 / 1000000000000) (25089092736 / 1000000000000), orderedInterval (73067423493 / 1000000000000) (73067423494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1155154433451723 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24422757711 / 1000000000000) (24422757712 / 1000000000000), orderedInterval (40057334595 / 1000000000000) (40057334596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1577264621688171 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27076685798 / 1000000000000) (-27076673477 / 1000000000000), orderedInterval (29721769913 / 1000000000000) (29721782235 / 1000000000000)))) (orderedInterval (-2031437914 / 1000000000000) (-2031436766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (666928723108977 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52406419370 / 1000000000000) (-52406419369 / 1000000000000), orderedInterval (-32580855946 / 1000000000000) (-32580855945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2711028232662417 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1278917702 / 1000000000000) (-1278917701 / 1000000000000), orderedInterval (30622315320 / 1000000000000) (30622315321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1810841219353503 / 4000000000000) 2 (IntervalRat.scale (729 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33523039739 / 1000000000000) (33523039740 / 1000000000000), orderedInterval (16769112509 / 1000000000000) (16769112510 / 1000000000000)))) (orderedInterval (9432340097 / 1000000000000) (9432340307 / 1000000000000))) = true
  rfl'

theorem compactCertificate493_chunkChecks2 :
    compactCertificate493.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate493.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate493_chunkChecks2_0
    compactCertificate493_chunkChecks2_1 compactCertificate493_chunkChecks2_2

theorem compactCertificate493_chunkChecks3_0 :
    compactCertificate493.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (729 / 2) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31679986424 / 1000000000000) (31679986425 / 1000000000000), orderedInterval (27213368467 / 1000000000000) (27213368468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1073956201019829 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38233642586 / 1000000000000) (-38233546087 / 1000000000000), orderedInterval (30225939232 / 1000000000000) (30226035731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (347295369587157 / 800000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37482710955 / 1000000000000) (37482710974 / 1000000000000), orderedInterval (7799565293 / 1000000000000) (7799565312 / 1000000000000)))) (orderedInterval (-11629557147 / 1000000000000) (-11629556746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (313377740972703 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50033716690 / 1000000000000) (-50033716689 / 1000000000000), orderedInterval (-74664692181 / 1000000000000) (-74664692180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2285587468965447 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13371927433 / 1000000000000) (13371927434 / 1000000000000), orderedInterval (30571599324 / 1000000000000) (30571599325 / 1000000000000)))) (orderedInterval (8640814017 / 1000000000000) (8640814121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1683553384957311 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25055640805 / 1000000000000) (25055640806 / 1000000000000), orderedInterval (29715439048 / 1000000000000) (29715439049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2884797420372603 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16325133748 / 1000000000000) (-16325133424 / 1000000000000), orderedInterval (24834972120 / 1000000000000) (24834972445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2124928723108977 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30663847914 / 1000000000000) (-30663847913 / 1000000000000), orderedInterval (-16036985540 / 1000000000000) (-16036985539 / 1000000000000)))) (orderedInterval (7134357926 / 1000000000000) (7134358120 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate493_chunkChecks3_1 :
    compactCertificate493.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3260187111194271 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23242776431 / 1000000000000) (-23242760041 / 1000000000000), orderedInterval (15533830889 / 1000000000000) (15533847279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1882269906256359 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4173451232 / 1000000000000) (4173451233 / 1000000000000), orderedInterval (36539508156 / 1000000000000) (36539508157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3340120979333331 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4176631511 / 1000000000000) (4176631512 / 1000000000000), orderedInterval (27291219158 / 1000000000000) (27291219159 / 1000000000000)))) (orderedInterval (-21543387080 / 1000000000000) (-21543353071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3120774287991039 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27347579884 / 1000000000000) (27347629496 / 1000000000000), orderedInterval (-8268916531 / 1000000000000) (-8268866919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2227131787747887 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33743558705 / 1000000000000) (-33743558370 / 1000000000000), orderedInterval (-2151736996 / 1000000000000) (-2151736661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2525330077434873 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19409112350 / 1000000000000) (-19409112349 / 1000000000000), orderedInterval (-25117499160 / 1000000000000) (-25117499159 / 1000000000000)))) (orderedInterval (-1424980028 / 1000000000000) (-1424970922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2105356939669737 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21410094075 / 1000000000000) (-21410091289 / 1000000000000), orderedInterval (27427120155 / 1000000000000) (27427122941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1860146705268477 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28186388584 / 1000000000000) (28186388585 / 1000000000000), orderedInterval (23938302597 / 1000000000000) (23938302598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (539143017887223 / 800000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20460369619 / 1000000000000) (20460372126 / 1000000000000), orderedInterval (-22950150130 / 1000000000000) (-22950147623 / 1000000000000)))) (orderedInterval (5601490851 / 1000000000000) (5601491471 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate493_chunkChecks3_2 :
    compactCertificate493.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1491297961018581 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9821392438 / 1000000000000) (9821392470 / 1000000000000), orderedInterval (-40151688027 / 1000000000000) (-40151687995 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1264189797228141 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20262234244 / 1000000000000) (20262235260 / 1000000000000), orderedInterval (-40079033592 / 1000000000000) (-40079032576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (791071276891023 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33528917181 / 1000000000000) (-33528917180 / 1000000000000), orderedInterval (-45684664288 / 1000000000000) (-45684664287 / 1000000000000)))) (orderedInterval (-8118773844 / 1000000000000) (-8118773723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (425440763696241 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25089092735 / 1000000000000) (25089092736 / 1000000000000), orderedInterval (73067423493 / 1000000000000) (73067423494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1155154433451723 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24422757711 / 1000000000000) (24422757712 / 1000000000000), orderedInterval (40057334595 / 1000000000000) (40057334596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1577264621688171 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27076685798 / 1000000000000) (-27076673477 / 1000000000000), orderedInterval (29721769913 / 1000000000000) (29721782235 / 1000000000000)))) (orderedInterval (3374830019 / 1000000000000) (3374831258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (666928723108977 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52406419370 / 1000000000000) (-52406419369 / 1000000000000), orderedInterval (-32580855946 / 1000000000000) (-32580855945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2711028232662417 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1278917702 / 1000000000000) (-1278917701 / 1000000000000), orderedInterval (30622315320 / 1000000000000) (30622315321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1810841219353503 / 4000000000000) 3 (IntervalRat.scale (729 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33523039739 / 1000000000000) (33523039740 / 1000000000000), orderedInterval (16769112509 / 1000000000000) (16769112510 / 1000000000000)))) (orderedInterval (22045976878 / 1000000000000) (22045977202 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate493_chunkChecks3 :
    compactCertificate493.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate493.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate493_chunkChecks3_0
    compactCertificate493_chunkChecks3_1 compactCertificate493_chunkChecks3_2

theorem compactCertificate493_chunkChecks4_0 :
    compactCertificate493.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (729 / 2) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31679986424 / 1000000000000) (31679986425 / 1000000000000), orderedInterval (27213368467 / 1000000000000) (27213368468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1073956201019829 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38233642586 / 1000000000000) (-38233546087 / 1000000000000), orderedInterval (30225939232 / 1000000000000) (30226035731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (347295369587157 / 800000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (37482710955 / 1000000000000) (37482710974 / 1000000000000), orderedInterval (7799565293 / 1000000000000) (7799565312 / 1000000000000)))) (orderedInterval (16941286188 / 1000000000000) (16941286502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (313377740972703 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-50033716690 / 1000000000000) (-50033716689 / 1000000000000), orderedInterval (-74664692181 / 1000000000000) (-74664692180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (841776692478291 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37178628846 / 1000000000000) (-37178628845 / 1000000000000), orderedInterval (-40444055659 / 1000000000000) (-40444055658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2285587468965447 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13371927433 / 1000000000000) (13371927434 / 1000000000000), orderedInterval (30571599324 / 1000000000000) (30571599325 / 1000000000000)))) (orderedInterval (-5937718273 / 1000000000000) (-5937718113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1683553384957311 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25055640805 / 1000000000000) (25055640806 / 1000000000000), orderedInterval (29715439048 / 1000000000000) (29715439049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2884797420372603 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16325133748 / 1000000000000) (-16325133424 / 1000000000000), orderedInterval (24834972120 / 1000000000000) (24834972445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2124928723108977 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30663847914 / 1000000000000) (-30663847913 / 1000000000000), orderedInterval (-16036985540 / 1000000000000) (-16036985539 / 1000000000000)))) (orderedInterval (4334424130 / 1000000000000) (4334424497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate493_chunkChecks4_1 :
    compactCertificate493.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3260187111194271 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23242776431 / 1000000000000) (-23242760041 / 1000000000000), orderedInterval (15533830889 / 1000000000000) (15533847279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1882269906256359 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4173451232 / 1000000000000) (4173451233 / 1000000000000), orderedInterval (36539508156 / 1000000000000) (36539508157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3340120979333331 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4176631511 / 1000000000000) (4176631512 / 1000000000000), orderedInterval (27291219158 / 1000000000000) (27291219159 / 1000000000000)))) (orderedInterval (120579371235 / 1000000000000) (120579447347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3120774287991039 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27347579884 / 1000000000000) (27347629496 / 1000000000000), orderedInterval (-8268916531 / 1000000000000) (-8268866919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2227131787747887 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33743558705 / 1000000000000) (-33743558370 / 1000000000000), orderedInterval (-2151736996 / 1000000000000) (-2151736661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2525330077434873 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-19409112350 / 1000000000000) (-19409112349 / 1000000000000), orderedInterval (-25117499160 / 1000000000000) (-25117499159 / 1000000000000)))) (orderedInterval (-26843848205 / 1000000000000) (-26843828840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2105356939669737 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21410094075 / 1000000000000) (-21410091289 / 1000000000000), orderedInterval (27427120155 / 1000000000000) (27427122941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1860146705268477 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28186388584 / 1000000000000) (28186388585 / 1000000000000), orderedInterval (23938302597 / 1000000000000) (23938302598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (539143017887223 / 800000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (20460369619 / 1000000000000) (20460372126 / 1000000000000), orderedInterval (-22950150130 / 1000000000000) (-22950147623 / 1000000000000)))) (orderedInterval (742604758 / 1000000000000) (742605834 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate493_chunkChecks4_2 :
    compactCertificate493.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1491297961018581 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9821392438 / 1000000000000) (9821392470 / 1000000000000), orderedInterval (-40151688027 / 1000000000000) (-40151687995 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1264189797228141 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (20262234244 / 1000000000000) (20262235260 / 1000000000000), orderedInterval (-40079033592 / 1000000000000) (-40079032576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (791071276891023 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33528917181 / 1000000000000) (-33528917180 / 1000000000000), orderedInterval (-45684664288 / 1000000000000) (-45684664287 / 1000000000000)))) (orderedInterval (-2417060686 / 1000000000000) (-2417060570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (425440763696241 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25089092735 / 1000000000000) (25089092736 / 1000000000000), orderedInterval (73067423493 / 1000000000000) (73067423494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1155154433451723 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24422757711 / 1000000000000) (24422757712 / 1000000000000), orderedInterval (40057334595 / 1000000000000) (40057334596 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1577264621688171 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27076685798 / 1000000000000) (-27076673477 / 1000000000000), orderedInterval (29721769913 / 1000000000000) (29721782235 / 1000000000000)))) (orderedInterval (2601841151 / 1000000000000) (2601842493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (666928723108977 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-52406419370 / 1000000000000) (-52406419369 / 1000000000000), orderedInterval (-32580855946 / 1000000000000) (-32580855945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2711028232662417 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-1278917702 / 1000000000000) (-1278917701 / 1000000000000), orderedInterval (30622315320 / 1000000000000) (30622315321 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1810841219353503 / 4000000000000) 4 (IntervalRat.scale (729 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33523039739 / 1000000000000) (33523039740 / 1000000000000), orderedInterval (16769112509 / 1000000000000) (16769112510 / 1000000000000)))) (orderedInterval (-13857063853 / 1000000000000) (-13857063333 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate493_chunkChecks4 :
    compactCertificate493.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate493.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate493_chunkChecks4_0
    compactCertificate493_chunkChecks4_1 compactCertificate493_chunkChecks4_2

theorem compactCertificate493_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate493.chunkCheck r b = true :=
  compactCertificate493.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate493_chunkChecks0
    · exact compactCertificate493_chunkChecks1
    · exact compactCertificate493_chunkChecks2
    · exact compactCertificate493_chunkChecks3
    · exact compactCertificate493_chunkChecks4)

theorem compactCertificate493_coefficient0 :
    compactCertificate493.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate493_coefficient1 :
    compactCertificate493.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate493_coefficient2 :
    compactCertificate493.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate493_coefficient3 :
    compactCertificate493.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate493_coefficient4 :
    compactCertificate493.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate493_coefficients : ∀ r : Fin 5,
    compactCertificate493.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate493_coefficient0
  · exact compactCertificate493_coefficient1
  · exact compactCertificate493_coefficient2
  · exact compactCertificate493_coefficient3
  · exact compactCertificate493_coefficient4

theorem compactCertificate493_lower : (1 : ℚ) ≤ compactCertificate493.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate493, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate493_proves {t : ℝ} (ht : t ∈ compactCertificate493.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate493.proves compactCertificate493_states compactCertificate493_chunks
    compactCertificate493_coefficients compactCertificate493_lower ht

end Erdos232
