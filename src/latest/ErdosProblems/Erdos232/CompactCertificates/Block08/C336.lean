/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate336 : CompactCertificate where
  left := 208
  right := 209
  center := 417 / 2
  grid := fun i =>
    match i.val with
    | 0 => 66
    | 1 => 49
    | 2 => 79
    | 3 => 14
    | 4 => 38
    | 5 => 104
    | 6 => 77
    | 7 => 131
    | 8 => 97
    | 9 => 148
    | 10 => 86
    | 11 => 152
    | 12 => 142
    | 13 => 101
    | 14 => 115
    | 15 => 96
    | 16 => 85
    | 17 => 123
    | 18 => 68
    | 19 => 58
    | 20 => 36
    | 21 => 19
    | 22 => 53
    | 23 => 72
    | 24 => 30
    | 25 => 123
    | _ => 82
  point := fun i =>
    match i.val with
    | 0 => 417 / 2
    | 1 => 614320625274717 / 4000000000000
    | 2 => 198658668200061 / 800000000000
    | 3 => 179257226317719 / 4000000000000
    | 4 => 481510124504043 / 4000000000000
    | 5 => 1307393655087231 / 4000000000000
    | 6 => 963020249008503 / 4000000000000
    | 7 => 1650151610830419 / 4000000000000
    | 8 => 1215494207868921 / 4000000000000
    | 9 => 1864880693234583 / 4000000000000
    | 10 => 1076689370245407 / 4000000000000
    | 11 => 1910604181593963 / 4000000000000
    | 12 => 1785134263501047 / 4000000000000
    | 13 => 1273956043197351 / 4000000000000
    | 14 => 1444530373512129 / 4000000000000
    | 15 => 1204298825572401 / 4000000000000
    | 16 => 1064034535112421 / 4000000000000
    | 17 => 308398681013679 / 800000000000
    | 18 => 853046981817213 / 4000000000000
    | 19 => 723137373723093 / 4000000000000
    | 20 => 452505792131079 / 4000000000000
    | 21 => 243359119974393 / 4000000000000
    | 22 => 660767350822179 / 4000000000000
    | 23 => 902221326809283 / 4000000000000
    | 24 => 381494207868921 / 4000000000000
    | 25 => 1550752775062041 / 4000000000000
    | _ => 1035830985556119 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (51539706637 / 1000000000000) (51539713118 / 1000000000000), orderedInterval (-20048057118 / 1000000000000) (-20048050637 / 1000000000000))
    | 1 => (orderedInterval (-26646167036 / 1000000000000) (-26646167035 / 1000000000000), orderedInterval (-58523759504 / 1000000000000) (-58523759503 / 1000000000000))
    | 2 => (orderedInterval (-40357257112 / 1000000000000) (-40357257111 / 1000000000000), orderedInterval (-30495908146 / 1000000000000) (-30495908145 / 1000000000000))
    | 3 => (orderedInterval (119069647245 / 1000000000000) (119069647287 / 1000000000000), orderedInterval (-6549933968 / 1000000000000) (-6549933925 / 1000000000000))
    | 4 => (orderedInterval (71115598118 / 1000000000000) (71115598784 / 1000000000000), orderedInterval (-15495926969 / 1000000000000) (-15495926303 / 1000000000000))
    | 5 => (orderedInterval (34783571779 / 1000000000000) (34783571780 / 1000000000000), orderedInterval (27110275194 / 1000000000000) (27110275195 / 1000000000000))
    | 6 => (orderedInterval (18244309597 / 1000000000000) (18244310040 / 1000000000000), orderedInterval (-48115043579 / 1000000000000) (-48115043136 / 1000000000000))
    | 7 => (orderedInterval (-38472193252 / 1000000000000) (-38472189892 / 1000000000000), orderedInterval (7988181874 / 1000000000000) (7988185234 / 1000000000000))
    | 8 => (orderedInterval (3472926646 / 1000000000000) (3472926651 / 1000000000000), orderedInterval (-45645138033 / 1000000000000) (-45645138028 / 1000000000000))
    | 9 => (orderedInterval (32797241589 / 1000000000000) (32797304192 / 1000000000000), orderedInterval (-17059600446 / 1000000000000) (-17059537843 / 1000000000000))
    | 10 => (orderedInterval (-10598375703 / 1000000000000) (-10598375651 / 1000000000000), orderedInterval (47483137130 / 1000000000000) (47483137182 / 1000000000000))
    | 11 => (orderedInterval (28914563460 / 1000000000000) (28914563461 / 1000000000000), orderedInterval (22257876434 / 1000000000000) (22257876435 / 1000000000000))
    | 12 => (orderedInterval (30994616573 / 1000000000000) (30994616574 / 1000000000000), orderedInterval (21548255709 / 1000000000000) (21548255710 / 1000000000000))
    | 13 => (orderedInterval (-41138256343 / 1000000000000) (-41138240604 / 1000000000000), orderedInterval (17572229050 / 1000000000000) (17572244789 / 1000000000000))
    | 14 => (orderedInterval (-24888032441 / 1000000000000) (-24888032440 / 1000000000000), orderedInterval (-33780161902 / 1000000000000) (-33780161901 / 1000000000000))
    | 15 => (orderedInterval (12123145104 / 1000000000000) (12123145105 / 1000000000000), orderedInterval (44336635466 / 1000000000000) (44336635467 / 1000000000000))
    | 16 => (orderedInterval (11714712510 / 1000000000000) (11714712583 / 1000000000000), orderedInterval (-47519377080 / 1000000000000) (-47519377007 / 1000000000000))
    | 17 => (orderedInterval (5367588106 / 1000000000000) (5367588112 / 1000000000000), orderedInterval (-40288602347 / 1000000000000) (-40288602341 / 1000000000000))
    | 18 => (orderedInterval (22191623579 / 1000000000000) (22191623580 / 1000000000000), orderedInterval (49874860225 / 1000000000000) (49874860226 / 1000000000000))
    | 19 => (orderedInterval (-35596510332 / 1000000000000) (-35596496502 / 1000000000000), orderedInterval (47578171616 / 1000000000000) (47578185446 / 1000000000000))
    | 20 => (orderedInterval (54509214702 / 1000000000000) (54509214703 / 1000000000000), orderedInterval (51297888854 / 1000000000000) (51297888855 / 1000000000000))
    | 21 => (orderedInterval (-95659459209 / 1000000000000) (-95659456453 / 1000000000000), orderedInterval (37019751775 / 1000000000000) (37019754531 / 1000000000000))
    | 22 => (orderedInterval (31272143323 / 1000000000000) (31272147970 / 1000000000000), orderedInterval (-53721911415 / 1000000000000) (-53721906768 / 1000000000000))
    | 23 => (orderedInterval (7702935185 / 1000000000000) (7702935187 / 1000000000000), orderedInterval (52548373574 / 1000000000000) (52548373575 / 1000000000000))
    | 24 => (orderedInterval (77048718152 / 1000000000000) (77048720725 / 1000000000000), orderedInterval (-27578121806 / 1000000000000) (-27578119233 / 1000000000000))
    | 25 => (orderedInterval (-35819625266 / 1000000000000) (-35819577957 / 1000000000000), orderedInterval (18994722246 / 1000000000000) (18994769555 / 1000000000000))
    | _ => (orderedInterval (41975261013 / 1000000000000) (41975312484 / 1000000000000), orderedInterval (-26471707827 / 1000000000000) (-26471656357 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17812035015 / 1000000000000) (17812037599 / 1000000000000)
      | 1 => orderedInterval (-1168018241 / 1000000000000) (-1168018190 / 1000000000000)
      | 2 => orderedInterval (1270570042 / 1000000000000) (1270570158 / 1000000000000)
      | 3 => orderedInterval (-2502561867 / 1000000000000) (-2502550656 / 1000000000000)
      | 4 => orderedInterval (-4323752134 / 1000000000000) (-4323750620 / 1000000000000)
      | 5 => orderedInterval (-392968547 / 1000000000000) (-392968522 / 1000000000000)
      | 6 => orderedInterval (241049480 / 1000000000000) (241050316 / 1000000000000)
      | 7 => orderedInterval (466551889 / 1000000000000) (466552071 / 1000000000000)
      | _ => orderedInterval (-4495429888 / 1000000000000) (-4495416306 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10479368453 / 1000000000000) (-10479365867 / 1000000000000)
      | 1 => orderedInterval (-3332588927 / 1000000000000) (-3332588884 / 1000000000000)
      | 2 => orderedInterval (-2095267251 / 1000000000000) (-2095267025 / 1000000000000)
      | 3 => orderedInterval (18568580017 / 1000000000000) (18568605067 / 1000000000000)
      | 4 => orderedInterval (2001686298 / 1000000000000) (2001688613 / 1000000000000)
      | 5 => orderedInterval (2301503018 / 1000000000000) (2301503053 / 1000000000000)
      | 6 => orderedInterval (-9585588649 / 1000000000000) (-9585587921 / 1000000000000)
      | 7 => orderedInterval (-3590517980 / 1000000000000) (-3590517859 / 1000000000000)
      | _ => orderedInterval (3217673829 / 1000000000000) (3217693073 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16884305326 / 1000000000000) (-16884302726 / 1000000000000)
      | 1 => orderedInterval (5286751574 / 1000000000000) (5286751622 / 1000000000000)
      | 2 => orderedInterval (-4813742391 / 1000000000000) (-4813741947 / 1000000000000)
      | 3 => orderedInterval (8786043139 / 1000000000000) (8786099252 / 1000000000000)
      | 4 => orderedInterval (11253155753 / 1000000000000) (11253159305 / 1000000000000)
      | 5 => orderedInterval (318459909 / 1000000000000) (318459960 / 1000000000000)
      | 6 => orderedInterval (1721041823 / 1000000000000) (1721042462 / 1000000000000)
      | 7 => orderedInterval (1003042783 / 1000000000000) (1003042877 / 1000000000000)
      | _ => orderedInterval (1955078862 / 1000000000000) (1955107289 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11268281503 / 1000000000000) (11268284107 / 1000000000000)
      | 1 => orderedInterval (7507144091 / 1000000000000) (7507144156 / 1000000000000)
      | 2 => orderedInterval (5346582320 / 1000000000000) (5346583191 / 1000000000000)
      | 3 => orderedInterval (-79544212644 / 1000000000000) (-79544087196 / 1000000000000)
      | 4 => orderedInterval (-3049946514 / 1000000000000) (-3049941078 / 1000000000000)
      | 5 => orderedInterval (-670441170 / 1000000000000) (-670441094 / 1000000000000)
      | 6 => orderedInterval (10013790989 / 1000000000000) (10013791547 / 1000000000000)
      | 7 => orderedInterval (4504532446 / 1000000000000) (4504532524 / 1000000000000)
      | _ => orderedInterval (431050148 / 1000000000000) (431093728 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15481931239 / 1000000000000) (15481933859 / 1000000000000)
      | 1 => orderedInterval (-14718958509 / 1000000000000) (-14718958414 / 1000000000000)
      | 2 => orderedInterval (18513780061 / 1000000000000) (18513781780 / 1000000000000)
      | 3 => orderedInterval (-33896152334 / 1000000000000) (-33895871249 / 1000000000000)
      | 4 => orderedInterval (-31761777938 / 1000000000000) (-31761769587 / 1000000000000)
      | 5 => orderedInterval (444945213 / 1000000000000) (444945332 / 1000000000000)
      | 6 => orderedInterval (-2687130345 / 1000000000000) (-2687129853 / 1000000000000)
      | 7 => orderedInterval (-1118456536 / 1000000000000) (-1118456468 / 1000000000000)
      | _ => orderedInterval (16130438919 / 1000000000000) (16130508645 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (6907475749 / 1000000000000) (6907505850 / 1000000000000)
    | 1 => orderedInterval (-2993888098 / 1000000000000) (-2993837750 / 1000000000000)
    | 2 => orderedInterval (8625526126 / 1000000000000) (8625618094 / 1000000000000)
    | 3 => orderedInterval (-44193218831 / 1000000000000) (-44193040115 / 1000000000000)
    | _ => orderedInterval (-33611380230 / 1000000000000) (-33611015955 / 1000000000000)

theorem compactCertificate336_stateChecks0 :
    compactCertificate336.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (417 / 2)) (orderedInterval (51539706637 / 1000000000000) (51539713118 / 1000000000000), orderedInterval (-20048057118 / 1000000000000) (-20048050637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (614320625274717 / 4000000000000)) (orderedInterval (-26646167036 / 1000000000000) (-26646167035 / 1000000000000), orderedInterval (-58523759504 / 1000000000000) (-58523759503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (198658668200061 / 800000000000)) (orderedInterval (-40357257112 / 1000000000000) (-40357257111 / 1000000000000), orderedInterval (-30495908146 / 1000000000000) (-30495908145 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks1 :
    compactCertificate336.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (179257226317719 / 4000000000000)) (orderedInterval (119069647245 / 1000000000000) (119069647287 / 1000000000000), orderedInterval (-6549933968 / 1000000000000) (-6549933925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (481510124504043 / 4000000000000)) (orderedInterval (71115598118 / 1000000000000) (71115598784 / 1000000000000), orderedInterval (-15495926969 / 1000000000000) (-15495926303 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1307393655087231 / 4000000000000)) (orderedInterval (34783571779 / 1000000000000) (34783571780 / 1000000000000), orderedInterval (27110275194 / 1000000000000) (27110275195 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks2 :
    compactCertificate336.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (963020249008503 / 4000000000000)) (orderedInterval (18244309597 / 1000000000000) (18244310040 / 1000000000000), orderedInterval (-48115043579 / 1000000000000) (-48115043136 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1650151610830419 / 4000000000000)) (orderedInterval (-38472193252 / 1000000000000) (-38472189892 / 1000000000000), orderedInterval (7988181874 / 1000000000000) (7988185234 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1215494207868921 / 4000000000000)) (orderedInterval (3472926646 / 1000000000000) (3472926651 / 1000000000000), orderedInterval (-45645138033 / 1000000000000) (-45645138028 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks3 :
    compactCertificate336.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1864880693234583 / 4000000000000)) (orderedInterval (32797241589 / 1000000000000) (32797304192 / 1000000000000), orderedInterval (-17059600446 / 1000000000000) (-17059537843 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1076689370245407 / 4000000000000)) (orderedInterval (-10598375703 / 1000000000000) (-10598375651 / 1000000000000), orderedInterval (47483137130 / 1000000000000) (47483137182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1910604181593963 / 4000000000000)) (orderedInterval (28914563460 / 1000000000000) (28914563461 / 1000000000000), orderedInterval (22257876434 / 1000000000000) (22257876435 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks4 :
    compactCertificate336.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1785134263501047 / 4000000000000)) (orderedInterval (30994616573 / 1000000000000) (30994616574 / 1000000000000), orderedInterval (21548255709 / 1000000000000) (21548255710 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1273956043197351 / 4000000000000)) (orderedInterval (-41138256343 / 1000000000000) (-41138240604 / 1000000000000), orderedInterval (17572229050 / 1000000000000) (17572244789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1444530373512129 / 4000000000000)) (orderedInterval (-24888032441 / 1000000000000) (-24888032440 / 1000000000000), orderedInterval (-33780161902 / 1000000000000) (-33780161901 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks5 :
    compactCertificate336.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1204298825572401 / 4000000000000)) (orderedInterval (12123145104 / 1000000000000) (12123145105 / 1000000000000), orderedInterval (44336635466 / 1000000000000) (44336635467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1064034535112421 / 4000000000000)) (orderedInterval (11714712510 / 1000000000000) (11714712583 / 1000000000000), orderedInterval (-47519377080 / 1000000000000) (-47519377007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308398681013679 / 800000000000)) (orderedInterval (5367588106 / 1000000000000) (5367588112 / 1000000000000), orderedInterval (-40288602347 / 1000000000000) (-40288602341 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks6 :
    compactCertificate336.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (853046981817213 / 4000000000000)) (orderedInterval (22191623579 / 1000000000000) (22191623580 / 1000000000000), orderedInterval (49874860225 / 1000000000000) (49874860226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (723137373723093 / 4000000000000)) (orderedInterval (-35596510332 / 1000000000000) (-35596496502 / 1000000000000), orderedInterval (47578171616 / 1000000000000) (47578185446 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (452505792131079 / 4000000000000)) (orderedInterval (54509214702 / 1000000000000) (54509214703 / 1000000000000), orderedInterval (51297888854 / 1000000000000) (51297888855 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks7 :
    compactCertificate336.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (243359119974393 / 4000000000000)) (orderedInterval (-95659459209 / 1000000000000) (-95659456453 / 1000000000000), orderedInterval (37019751775 / 1000000000000) (37019754531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (660767350822179 / 4000000000000)) (orderedInterval (31272143323 / 1000000000000) (31272147970 / 1000000000000), orderedInterval (-53721911415 / 1000000000000) (-53721906768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (902221326809283 / 4000000000000)) (orderedInterval (7702935185 / 1000000000000) (7702935187 / 1000000000000), orderedInterval (52548373574 / 1000000000000) (52548373575 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_stateChecks8 :
    compactCertificate336.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (381494207868921 / 4000000000000)) (orderedInterval (77048718152 / 1000000000000) (77048720725 / 1000000000000), orderedInterval (-27578121806 / 1000000000000) (-27578119233 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1550752775062041 / 4000000000000)) (orderedInterval (-35819625266 / 1000000000000) (-35819577957 / 1000000000000), orderedInterval (18994722246 / 1000000000000) (18994769555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1035830985556119 / 4000000000000)) (orderedInterval (41975261013 / 1000000000000) (41975312484 / 1000000000000), orderedInterval (-26471707827 / 1000000000000) (-26471656357 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_states : ∀ j,
    BesselStateValid (compactCertificate336.point j) (compactCertificate336.state j) :=
  compactCertificate336.statesValid_of_checks3 compactCertificate336_stateChecks0
    compactCertificate336_stateChecks1 compactCertificate336_stateChecks2
    compactCertificate336_stateChecks3 compactCertificate336_stateChecks4
    compactCertificate336_stateChecks5 compactCertificate336_stateChecks6
    compactCertificate336_stateChecks7 compactCertificate336_stateChecks8

theorem compactCertificate336_chunkChecks0_0 :
    compactCertificate336.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (417 / 2) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51539706637 / 1000000000000) (51539713118 / 1000000000000), orderedInterval (-20048057118 / 1000000000000) (-20048050637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (614320625274717 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26646167036 / 1000000000000) (-26646167035 / 1000000000000), orderedInterval (-58523759504 / 1000000000000) (-58523759503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (198658668200061 / 800000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40357257112 / 1000000000000) (-40357257111 / 1000000000000), orderedInterval (-30495908146 / 1000000000000) (-30495908145 / 1000000000000)))) (orderedInterval (17812035015 / 1000000000000) (17812037599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (179257226317719 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119069647245 / 1000000000000) (119069647287 / 1000000000000), orderedInterval (-6549933968 / 1000000000000) (-6549933925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (481510124504043 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598784 / 1000000000000), orderedInterval (-15495926969 / 1000000000000) (-15495926303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1307393655087231 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34783571779 / 1000000000000) (34783571780 / 1000000000000), orderedInterval (27110275194 / 1000000000000) (27110275195 / 1000000000000)))) (orderedInterval (-1168018241 / 1000000000000) (-1168018190 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (963020249008503 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18244309597 / 1000000000000) (18244310040 / 1000000000000), orderedInterval (-48115043579 / 1000000000000) (-48115043136 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1650151610830419 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38472193252 / 1000000000000) (-38472189892 / 1000000000000), orderedInterval (7988181874 / 1000000000000) (7988185234 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1215494207868921 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3472926646 / 1000000000000) (3472926651 / 1000000000000), orderedInterval (-45645138033 / 1000000000000) (-45645138028 / 1000000000000)))) (orderedInterval (1270570042 / 1000000000000) (1270570158 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks0_1 :
    compactCertificate336.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1864880693234583 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32797241589 / 1000000000000) (32797304192 / 1000000000000), orderedInterval (-17059600446 / 1000000000000) (-17059537843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1076689370245407 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10598375703 / 1000000000000) (-10598375651 / 1000000000000), orderedInterval (47483137130 / 1000000000000) (47483137182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1910604181593963 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28914563460 / 1000000000000) (28914563461 / 1000000000000), orderedInterval (22257876434 / 1000000000000) (22257876435 / 1000000000000)))) (orderedInterval (-2502561867 / 1000000000000) (-2502550656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1785134263501047 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30994616573 / 1000000000000) (30994616574 / 1000000000000), orderedInterval (21548255709 / 1000000000000) (21548255710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1273956043197351 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41138256343 / 1000000000000) (-41138240604 / 1000000000000), orderedInterval (17572229050 / 1000000000000) (17572244789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1444530373512129 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24888032441 / 1000000000000) (-24888032440 / 1000000000000), orderedInterval (-33780161902 / 1000000000000) (-33780161901 / 1000000000000)))) (orderedInterval (-4323752134 / 1000000000000) (-4323750620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1204298825572401 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12123145104 / 1000000000000) (12123145105 / 1000000000000), orderedInterval (44336635466 / 1000000000000) (44336635467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1064034535112421 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11714712510 / 1000000000000) (11714712583 / 1000000000000), orderedInterval (-47519377080 / 1000000000000) (-47519377007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (308398681013679 / 800000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5367588106 / 1000000000000) (5367588112 / 1000000000000), orderedInterval (-40288602347 / 1000000000000) (-40288602341 / 1000000000000)))) (orderedInterval (-392968547 / 1000000000000) (-392968522 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks0_2 :
    compactCertificate336.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (853046981817213 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22191623579 / 1000000000000) (22191623580 / 1000000000000), orderedInterval (49874860225 / 1000000000000) (49874860226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (723137373723093 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35596510332 / 1000000000000) (-35596496502 / 1000000000000), orderedInterval (47578171616 / 1000000000000) (47578185446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (452505792131079 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54509214702 / 1000000000000) (54509214703 / 1000000000000), orderedInterval (51297888854 / 1000000000000) (51297888855 / 1000000000000)))) (orderedInterval (241049480 / 1000000000000) (241050316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (243359119974393 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95659459209 / 1000000000000) (-95659456453 / 1000000000000), orderedInterval (37019751775 / 1000000000000) (37019754531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (660767350822179 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31272143323 / 1000000000000) (31272147970 / 1000000000000), orderedInterval (-53721911415 / 1000000000000) (-53721906768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (902221326809283 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7702935185 / 1000000000000) (7702935187 / 1000000000000), orderedInterval (52548373574 / 1000000000000) (52548373575 / 1000000000000)))) (orderedInterval (466551889 / 1000000000000) (466552071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (381494207868921 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (77048718152 / 1000000000000) (77048720725 / 1000000000000), orderedInterval (-27578121806 / 1000000000000) (-27578119233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1550752775062041 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35819625266 / 1000000000000) (-35819577957 / 1000000000000), orderedInterval (18994722246 / 1000000000000) (18994769555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1035830985556119 / 4000000000000) 0 (IntervalRat.scale (417 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41975261013 / 1000000000000) (41975312484 / 1000000000000), orderedInterval (-26471707827 / 1000000000000) (-26471656357 / 1000000000000)))) (orderedInterval (-4495429888 / 1000000000000) (-4495416306 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks0 :
    compactCertificate336.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate336.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate336_chunkChecks0_0
    compactCertificate336_chunkChecks0_1 compactCertificate336_chunkChecks0_2

theorem compactCertificate336_chunkChecks1_0 :
    compactCertificate336.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (417 / 2) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51539706637 / 1000000000000) (51539713118 / 1000000000000), orderedInterval (-20048057118 / 1000000000000) (-20048050637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (614320625274717 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26646167036 / 1000000000000) (-26646167035 / 1000000000000), orderedInterval (-58523759504 / 1000000000000) (-58523759503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (198658668200061 / 800000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40357257112 / 1000000000000) (-40357257111 / 1000000000000), orderedInterval (-30495908146 / 1000000000000) (-30495908145 / 1000000000000)))) (orderedInterval (-10479368453 / 1000000000000) (-10479365867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (179257226317719 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119069647245 / 1000000000000) (119069647287 / 1000000000000), orderedInterval (-6549933968 / 1000000000000) (-6549933925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (481510124504043 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598784 / 1000000000000), orderedInterval (-15495926969 / 1000000000000) (-15495926303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1307393655087231 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34783571779 / 1000000000000) (34783571780 / 1000000000000), orderedInterval (27110275194 / 1000000000000) (27110275195 / 1000000000000)))) (orderedInterval (-3332588927 / 1000000000000) (-3332588884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (963020249008503 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18244309597 / 1000000000000) (18244310040 / 1000000000000), orderedInterval (-48115043579 / 1000000000000) (-48115043136 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1650151610830419 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38472193252 / 1000000000000) (-38472189892 / 1000000000000), orderedInterval (7988181874 / 1000000000000) (7988185234 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1215494207868921 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3472926646 / 1000000000000) (3472926651 / 1000000000000), orderedInterval (-45645138033 / 1000000000000) (-45645138028 / 1000000000000)))) (orderedInterval (-2095267251 / 1000000000000) (-2095267025 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks1_1 :
    compactCertificate336.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1864880693234583 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32797241589 / 1000000000000) (32797304192 / 1000000000000), orderedInterval (-17059600446 / 1000000000000) (-17059537843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1076689370245407 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10598375703 / 1000000000000) (-10598375651 / 1000000000000), orderedInterval (47483137130 / 1000000000000) (47483137182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1910604181593963 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28914563460 / 1000000000000) (28914563461 / 1000000000000), orderedInterval (22257876434 / 1000000000000) (22257876435 / 1000000000000)))) (orderedInterval (18568580017 / 1000000000000) (18568605067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1785134263501047 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30994616573 / 1000000000000) (30994616574 / 1000000000000), orderedInterval (21548255709 / 1000000000000) (21548255710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1273956043197351 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41138256343 / 1000000000000) (-41138240604 / 1000000000000), orderedInterval (17572229050 / 1000000000000) (17572244789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1444530373512129 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24888032441 / 1000000000000) (-24888032440 / 1000000000000), orderedInterval (-33780161902 / 1000000000000) (-33780161901 / 1000000000000)))) (orderedInterval (2001686298 / 1000000000000) (2001688613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1204298825572401 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12123145104 / 1000000000000) (12123145105 / 1000000000000), orderedInterval (44336635466 / 1000000000000) (44336635467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1064034535112421 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11714712510 / 1000000000000) (11714712583 / 1000000000000), orderedInterval (-47519377080 / 1000000000000) (-47519377007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (308398681013679 / 800000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5367588106 / 1000000000000) (5367588112 / 1000000000000), orderedInterval (-40288602347 / 1000000000000) (-40288602341 / 1000000000000)))) (orderedInterval (2301503018 / 1000000000000) (2301503053 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks1_2 :
    compactCertificate336.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (853046981817213 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22191623579 / 1000000000000) (22191623580 / 1000000000000), orderedInterval (49874860225 / 1000000000000) (49874860226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (723137373723093 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35596510332 / 1000000000000) (-35596496502 / 1000000000000), orderedInterval (47578171616 / 1000000000000) (47578185446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (452505792131079 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54509214702 / 1000000000000) (54509214703 / 1000000000000), orderedInterval (51297888854 / 1000000000000) (51297888855 / 1000000000000)))) (orderedInterval (-9585588649 / 1000000000000) (-9585587921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (243359119974393 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95659459209 / 1000000000000) (-95659456453 / 1000000000000), orderedInterval (37019751775 / 1000000000000) (37019754531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (660767350822179 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31272143323 / 1000000000000) (31272147970 / 1000000000000), orderedInterval (-53721911415 / 1000000000000) (-53721906768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (902221326809283 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7702935185 / 1000000000000) (7702935187 / 1000000000000), orderedInterval (52548373574 / 1000000000000) (52548373575 / 1000000000000)))) (orderedInterval (-3590517980 / 1000000000000) (-3590517859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (381494207868921 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (77048718152 / 1000000000000) (77048720725 / 1000000000000), orderedInterval (-27578121806 / 1000000000000) (-27578119233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1550752775062041 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35819625266 / 1000000000000) (-35819577957 / 1000000000000), orderedInterval (18994722246 / 1000000000000) (18994769555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1035830985556119 / 4000000000000) 1 (IntervalRat.scale (417 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41975261013 / 1000000000000) (41975312484 / 1000000000000), orderedInterval (-26471707827 / 1000000000000) (-26471656357 / 1000000000000)))) (orderedInterval (3217673829 / 1000000000000) (3217693073 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks1 :
    compactCertificate336.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate336.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate336_chunkChecks1_0
    compactCertificate336_chunkChecks1_1 compactCertificate336_chunkChecks1_2

theorem compactCertificate336_chunkChecks2_0 :
    compactCertificate336.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (417 / 2) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51539706637 / 1000000000000) (51539713118 / 1000000000000), orderedInterval (-20048057118 / 1000000000000) (-20048050637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (614320625274717 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26646167036 / 1000000000000) (-26646167035 / 1000000000000), orderedInterval (-58523759504 / 1000000000000) (-58523759503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (198658668200061 / 800000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40357257112 / 1000000000000) (-40357257111 / 1000000000000), orderedInterval (-30495908146 / 1000000000000) (-30495908145 / 1000000000000)))) (orderedInterval (-16884305326 / 1000000000000) (-16884302726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (179257226317719 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119069647245 / 1000000000000) (119069647287 / 1000000000000), orderedInterval (-6549933968 / 1000000000000) (-6549933925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (481510124504043 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598784 / 1000000000000), orderedInterval (-15495926969 / 1000000000000) (-15495926303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1307393655087231 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34783571779 / 1000000000000) (34783571780 / 1000000000000), orderedInterval (27110275194 / 1000000000000) (27110275195 / 1000000000000)))) (orderedInterval (5286751574 / 1000000000000) (5286751622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (963020249008503 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18244309597 / 1000000000000) (18244310040 / 1000000000000), orderedInterval (-48115043579 / 1000000000000) (-48115043136 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1650151610830419 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38472193252 / 1000000000000) (-38472189892 / 1000000000000), orderedInterval (7988181874 / 1000000000000) (7988185234 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1215494207868921 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3472926646 / 1000000000000) (3472926651 / 1000000000000), orderedInterval (-45645138033 / 1000000000000) (-45645138028 / 1000000000000)))) (orderedInterval (-4813742391 / 1000000000000) (-4813741947 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks2_1 :
    compactCertificate336.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1864880693234583 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32797241589 / 1000000000000) (32797304192 / 1000000000000), orderedInterval (-17059600446 / 1000000000000) (-17059537843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1076689370245407 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10598375703 / 1000000000000) (-10598375651 / 1000000000000), orderedInterval (47483137130 / 1000000000000) (47483137182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1910604181593963 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28914563460 / 1000000000000) (28914563461 / 1000000000000), orderedInterval (22257876434 / 1000000000000) (22257876435 / 1000000000000)))) (orderedInterval (8786043139 / 1000000000000) (8786099252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1785134263501047 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30994616573 / 1000000000000) (30994616574 / 1000000000000), orderedInterval (21548255709 / 1000000000000) (21548255710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1273956043197351 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41138256343 / 1000000000000) (-41138240604 / 1000000000000), orderedInterval (17572229050 / 1000000000000) (17572244789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1444530373512129 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24888032441 / 1000000000000) (-24888032440 / 1000000000000), orderedInterval (-33780161902 / 1000000000000) (-33780161901 / 1000000000000)))) (orderedInterval (11253155753 / 1000000000000) (11253159305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1204298825572401 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12123145104 / 1000000000000) (12123145105 / 1000000000000), orderedInterval (44336635466 / 1000000000000) (44336635467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1064034535112421 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11714712510 / 1000000000000) (11714712583 / 1000000000000), orderedInterval (-47519377080 / 1000000000000) (-47519377007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (308398681013679 / 800000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5367588106 / 1000000000000) (5367588112 / 1000000000000), orderedInterval (-40288602347 / 1000000000000) (-40288602341 / 1000000000000)))) (orderedInterval (318459909 / 1000000000000) (318459960 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks2_2 :
    compactCertificate336.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (853046981817213 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22191623579 / 1000000000000) (22191623580 / 1000000000000), orderedInterval (49874860225 / 1000000000000) (49874860226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (723137373723093 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35596510332 / 1000000000000) (-35596496502 / 1000000000000), orderedInterval (47578171616 / 1000000000000) (47578185446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (452505792131079 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54509214702 / 1000000000000) (54509214703 / 1000000000000), orderedInterval (51297888854 / 1000000000000) (51297888855 / 1000000000000)))) (orderedInterval (1721041823 / 1000000000000) (1721042462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (243359119974393 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95659459209 / 1000000000000) (-95659456453 / 1000000000000), orderedInterval (37019751775 / 1000000000000) (37019754531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (660767350822179 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31272143323 / 1000000000000) (31272147970 / 1000000000000), orderedInterval (-53721911415 / 1000000000000) (-53721906768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (902221326809283 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7702935185 / 1000000000000) (7702935187 / 1000000000000), orderedInterval (52548373574 / 1000000000000) (52548373575 / 1000000000000)))) (orderedInterval (1003042783 / 1000000000000) (1003042877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (381494207868921 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (77048718152 / 1000000000000) (77048720725 / 1000000000000), orderedInterval (-27578121806 / 1000000000000) (-27578119233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1550752775062041 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35819625266 / 1000000000000) (-35819577957 / 1000000000000), orderedInterval (18994722246 / 1000000000000) (18994769555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1035830985556119 / 4000000000000) 2 (IntervalRat.scale (417 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41975261013 / 1000000000000) (41975312484 / 1000000000000), orderedInterval (-26471707827 / 1000000000000) (-26471656357 / 1000000000000)))) (orderedInterval (1955078862 / 1000000000000) (1955107289 / 1000000000000))) = true
  rfl'

theorem compactCertificate336_chunkChecks2 :
    compactCertificate336.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate336.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate336_chunkChecks2_0
    compactCertificate336_chunkChecks2_1 compactCertificate336_chunkChecks2_2

theorem compactCertificate336_chunkChecks3_0 :
    compactCertificate336.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (417 / 2) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51539706637 / 1000000000000) (51539713118 / 1000000000000), orderedInterval (-20048057118 / 1000000000000) (-20048050637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (614320625274717 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26646167036 / 1000000000000) (-26646167035 / 1000000000000), orderedInterval (-58523759504 / 1000000000000) (-58523759503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (198658668200061 / 800000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40357257112 / 1000000000000) (-40357257111 / 1000000000000), orderedInterval (-30495908146 / 1000000000000) (-30495908145 / 1000000000000)))) (orderedInterval (11268281503 / 1000000000000) (11268284107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (179257226317719 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119069647245 / 1000000000000) (119069647287 / 1000000000000), orderedInterval (-6549933968 / 1000000000000) (-6549933925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (481510124504043 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598784 / 1000000000000), orderedInterval (-15495926969 / 1000000000000) (-15495926303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1307393655087231 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34783571779 / 1000000000000) (34783571780 / 1000000000000), orderedInterval (27110275194 / 1000000000000) (27110275195 / 1000000000000)))) (orderedInterval (7507144091 / 1000000000000) (7507144156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (963020249008503 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18244309597 / 1000000000000) (18244310040 / 1000000000000), orderedInterval (-48115043579 / 1000000000000) (-48115043136 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1650151610830419 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38472193252 / 1000000000000) (-38472189892 / 1000000000000), orderedInterval (7988181874 / 1000000000000) (7988185234 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1215494207868921 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3472926646 / 1000000000000) (3472926651 / 1000000000000), orderedInterval (-45645138033 / 1000000000000) (-45645138028 / 1000000000000)))) (orderedInterval (5346582320 / 1000000000000) (5346583191 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate336_chunkChecks3_1 :
    compactCertificate336.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1864880693234583 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32797241589 / 1000000000000) (32797304192 / 1000000000000), orderedInterval (-17059600446 / 1000000000000) (-17059537843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1076689370245407 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10598375703 / 1000000000000) (-10598375651 / 1000000000000), orderedInterval (47483137130 / 1000000000000) (47483137182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1910604181593963 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28914563460 / 1000000000000) (28914563461 / 1000000000000), orderedInterval (22257876434 / 1000000000000) (22257876435 / 1000000000000)))) (orderedInterval (-79544212644 / 1000000000000) (-79544087196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1785134263501047 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30994616573 / 1000000000000) (30994616574 / 1000000000000), orderedInterval (21548255709 / 1000000000000) (21548255710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1273956043197351 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41138256343 / 1000000000000) (-41138240604 / 1000000000000), orderedInterval (17572229050 / 1000000000000) (17572244789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1444530373512129 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24888032441 / 1000000000000) (-24888032440 / 1000000000000), orderedInterval (-33780161902 / 1000000000000) (-33780161901 / 1000000000000)))) (orderedInterval (-3049946514 / 1000000000000) (-3049941078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1204298825572401 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12123145104 / 1000000000000) (12123145105 / 1000000000000), orderedInterval (44336635466 / 1000000000000) (44336635467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1064034535112421 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11714712510 / 1000000000000) (11714712583 / 1000000000000), orderedInterval (-47519377080 / 1000000000000) (-47519377007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (308398681013679 / 800000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5367588106 / 1000000000000) (5367588112 / 1000000000000), orderedInterval (-40288602347 / 1000000000000) (-40288602341 / 1000000000000)))) (orderedInterval (-670441170 / 1000000000000) (-670441094 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate336_chunkChecks3_2 :
    compactCertificate336.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (853046981817213 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22191623579 / 1000000000000) (22191623580 / 1000000000000), orderedInterval (49874860225 / 1000000000000) (49874860226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (723137373723093 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35596510332 / 1000000000000) (-35596496502 / 1000000000000), orderedInterval (47578171616 / 1000000000000) (47578185446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (452505792131079 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54509214702 / 1000000000000) (54509214703 / 1000000000000), orderedInterval (51297888854 / 1000000000000) (51297888855 / 1000000000000)))) (orderedInterval (10013790989 / 1000000000000) (10013791547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (243359119974393 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95659459209 / 1000000000000) (-95659456453 / 1000000000000), orderedInterval (37019751775 / 1000000000000) (37019754531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (660767350822179 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31272143323 / 1000000000000) (31272147970 / 1000000000000), orderedInterval (-53721911415 / 1000000000000) (-53721906768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (902221326809283 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7702935185 / 1000000000000) (7702935187 / 1000000000000), orderedInterval (52548373574 / 1000000000000) (52548373575 / 1000000000000)))) (orderedInterval (4504532446 / 1000000000000) (4504532524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (381494207868921 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (77048718152 / 1000000000000) (77048720725 / 1000000000000), orderedInterval (-27578121806 / 1000000000000) (-27578119233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1550752775062041 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35819625266 / 1000000000000) (-35819577957 / 1000000000000), orderedInterval (18994722246 / 1000000000000) (18994769555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1035830985556119 / 4000000000000) 3 (IntervalRat.scale (417 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41975261013 / 1000000000000) (41975312484 / 1000000000000), orderedInterval (-26471707827 / 1000000000000) (-26471656357 / 1000000000000)))) (orderedInterval (431050148 / 1000000000000) (431093728 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate336_chunkChecks3 :
    compactCertificate336.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate336.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate336_chunkChecks3_0
    compactCertificate336_chunkChecks3_1 compactCertificate336_chunkChecks3_2

theorem compactCertificate336_chunkChecks4_0 :
    compactCertificate336.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (417 / 2) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51539706637 / 1000000000000) (51539713118 / 1000000000000), orderedInterval (-20048057118 / 1000000000000) (-20048050637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (614320625274717 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26646167036 / 1000000000000) (-26646167035 / 1000000000000), orderedInterval (-58523759504 / 1000000000000) (-58523759503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (198658668200061 / 800000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40357257112 / 1000000000000) (-40357257111 / 1000000000000), orderedInterval (-30495908146 / 1000000000000) (-30495908145 / 1000000000000)))) (orderedInterval (15481931239 / 1000000000000) (15481933859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (179257226317719 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (119069647245 / 1000000000000) (119069647287 / 1000000000000), orderedInterval (-6549933968 / 1000000000000) (-6549933925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (481510124504043 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (71115598118 / 1000000000000) (71115598784 / 1000000000000), orderedInterval (-15495926969 / 1000000000000) (-15495926303 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1307393655087231 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34783571779 / 1000000000000) (34783571780 / 1000000000000), orderedInterval (27110275194 / 1000000000000) (27110275195 / 1000000000000)))) (orderedInterval (-14718958509 / 1000000000000) (-14718958414 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (963020249008503 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (18244309597 / 1000000000000) (18244310040 / 1000000000000), orderedInterval (-48115043579 / 1000000000000) (-48115043136 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1650151610830419 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38472193252 / 1000000000000) (-38472189892 / 1000000000000), orderedInterval (7988181874 / 1000000000000) (7988185234 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1215494207868921 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (3472926646 / 1000000000000) (3472926651 / 1000000000000), orderedInterval (-45645138033 / 1000000000000) (-45645138028 / 1000000000000)))) (orderedInterval (18513780061 / 1000000000000) (18513781780 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate336_chunkChecks4_1 :
    compactCertificate336.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1864880693234583 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32797241589 / 1000000000000) (32797304192 / 1000000000000), orderedInterval (-17059600446 / 1000000000000) (-17059537843 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1076689370245407 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10598375703 / 1000000000000) (-10598375651 / 1000000000000), orderedInterval (47483137130 / 1000000000000) (47483137182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1910604181593963 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28914563460 / 1000000000000) (28914563461 / 1000000000000), orderedInterval (22257876434 / 1000000000000) (22257876435 / 1000000000000)))) (orderedInterval (-33896152334 / 1000000000000) (-33895871249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1785134263501047 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30994616573 / 1000000000000) (30994616574 / 1000000000000), orderedInterval (21548255709 / 1000000000000) (21548255710 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1273956043197351 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41138256343 / 1000000000000) (-41138240604 / 1000000000000), orderedInterval (17572229050 / 1000000000000) (17572244789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1444530373512129 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-24888032441 / 1000000000000) (-24888032440 / 1000000000000), orderedInterval (-33780161902 / 1000000000000) (-33780161901 / 1000000000000)))) (orderedInterval (-31761777938 / 1000000000000) (-31761769587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1204298825572401 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (12123145104 / 1000000000000) (12123145105 / 1000000000000), orderedInterval (44336635466 / 1000000000000) (44336635467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1064034535112421 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11714712510 / 1000000000000) (11714712583 / 1000000000000), orderedInterval (-47519377080 / 1000000000000) (-47519377007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (308398681013679 / 800000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (5367588106 / 1000000000000) (5367588112 / 1000000000000), orderedInterval (-40288602347 / 1000000000000) (-40288602341 / 1000000000000)))) (orderedInterval (444945213 / 1000000000000) (444945332 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate336_chunkChecks4_2 :
    compactCertificate336.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (853046981817213 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (22191623579 / 1000000000000) (22191623580 / 1000000000000), orderedInterval (49874860225 / 1000000000000) (49874860226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (723137373723093 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35596510332 / 1000000000000) (-35596496502 / 1000000000000), orderedInterval (47578171616 / 1000000000000) (47578185446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (452505792131079 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54509214702 / 1000000000000) (54509214703 / 1000000000000), orderedInterval (51297888854 / 1000000000000) (51297888855 / 1000000000000)))) (orderedInterval (-2687130345 / 1000000000000) (-2687129853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (243359119974393 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95659459209 / 1000000000000) (-95659456453 / 1000000000000), orderedInterval (37019751775 / 1000000000000) (37019754531 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (660767350822179 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31272143323 / 1000000000000) (31272147970 / 1000000000000), orderedInterval (-53721911415 / 1000000000000) (-53721906768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (902221326809283 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7702935185 / 1000000000000) (7702935187 / 1000000000000), orderedInterval (52548373574 / 1000000000000) (52548373575 / 1000000000000)))) (orderedInterval (-1118456536 / 1000000000000) (-1118456468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (381494207868921 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (77048718152 / 1000000000000) (77048720725 / 1000000000000), orderedInterval (-27578121806 / 1000000000000) (-27578119233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1550752775062041 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-35819625266 / 1000000000000) (-35819577957 / 1000000000000), orderedInterval (18994722246 / 1000000000000) (18994769555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1035830985556119 / 4000000000000) 4 (IntervalRat.scale (417 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (41975261013 / 1000000000000) (41975312484 / 1000000000000), orderedInterval (-26471707827 / 1000000000000) (-26471656357 / 1000000000000)))) (orderedInterval (16130438919 / 1000000000000) (16130508645 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate336_chunkChecks4 :
    compactCertificate336.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate336.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate336_chunkChecks4_0
    compactCertificate336_chunkChecks4_1 compactCertificate336_chunkChecks4_2

theorem compactCertificate336_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate336.chunkCheck r b = true :=
  compactCertificate336.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate336_chunkChecks0
    · exact compactCertificate336_chunkChecks1
    · exact compactCertificate336_chunkChecks2
    · exact compactCertificate336_chunkChecks3
    · exact compactCertificate336_chunkChecks4)

theorem compactCertificate336_coefficient0 :
    compactCertificate336.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate336_coefficient1 :
    compactCertificate336.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate336_coefficient2 :
    compactCertificate336.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate336_coefficient3 :
    compactCertificate336.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate336_coefficient4 :
    compactCertificate336.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate336_coefficients : ∀ r : Fin 5,
    compactCertificate336.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate336_coefficient0
  · exact compactCertificate336_coefficient1
  · exact compactCertificate336_coefficient2
  · exact compactCertificate336_coefficient3
  · exact compactCertificate336_coefficient4

theorem compactCertificate336_lower : (1 : ℚ) ≤ compactCertificate336.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate336, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate336_proves {t : ℝ} (ht : t ∈ compactCertificate336.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate336.proves compactCertificate336_states compactCertificate336_chunks
    compactCertificate336_coefficients compactCertificate336_lower ht

end Erdos232
