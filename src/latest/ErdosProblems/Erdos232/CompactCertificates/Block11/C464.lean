/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate464 : CompactCertificate where
  left := 335
  right := 336
  center := 671 / 2
  grid := fun i =>
    match i.val with
    | 0 => 107
    | 1 => 79
    | 2 => 127
    | 3 => 23
    | 4 => 62
    | 5 => 167
    | 6 => 123
    | 7 => 211
    | 8 => 156
    | 9 => 239
    | 10 => 138
    | 11 => 245
    | 12 => 229
    | 13 => 163
    | 14 => 185
    | 15 => 154
    | 16 => 136
    | 17 => 198
    | 18 => 109
    | 19 => 93
    | 20 => 58
    | 21 => 31
    | 22 => 85
    | 23 => 116
    | 24 => 49
    | 25 => 199
    | _ => 133
  point := fun i =>
    match i.val with
    | 0 => 671 / 2
    | 1 => 988511126041571 / 4000000000000
    | 2 => 319664187919043 / 800000000000
    | 3 => 288445081197097 / 4000000000000
    | 4 => 774804061252309 / 4000000000000
    | 5 => 2103743747154753 / 4000000000000
    | 6 => 1549608122505289 / 4000000000000
    | 7 => 2655279930137197 / 4000000000000
    | 8 => 1955867178609223 / 4000000000000
    | 9 => 3000803225804329 / 4000000000000
    | 10 => 1732514550203041 / 4000000000000
    | 11 => 3074377472061269 / 4000000000000
    | 12 => 2872482232156361 / 4000000000000
    | 13 => 2049938860876313 / 4000000000000
    | 14 => 2324412183756927 / 4000000000000
    | 15 => 1937852546664463 / 4000000000000
    | 16 => 1712151494149723 / 4000000000000
    | 17 => 496248237314577 / 800000000000
    | 18 => 1372648740526019 / 4000000000000
    | 19 => 1163609539012459 / 4000000000000
    | 20 => 728132821390777 / 4000000000000
    | 21 => 391592253004359 / 4000000000000
    | 22 => 1063249142450077 / 4000000000000
    | 23 => 1451775804050429 / 4000000000000
    | 24 => 613867178609223 / 4000000000000
    | 25 => 2495336000159783 / 4000000000000
    | _ => 1666768804096297 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-5846067571 / 1000000000000) (-5846067569 / 1000000000000), orderedInterval (-43157836256 / 1000000000000) (-43157836255 / 1000000000000))
    | 1 => (orderedInterval (13691765680 / 1000000000000) (13691765810 / 1000000000000), orderedInterval (-48901164376 / 1000000000000) (-48901164246 / 1000000000000))
    | 2 => (orderedInterval (-39213771246 / 1000000000000) (-39213771227 / 1000000000000), orderedInterval (-7400787936 / 1000000000000) (-7400787917 / 1000000000000))
    | 3 => (orderedInterval (-55983341774 / 1000000000000) (-55983341773 / 1000000000000), orderedInterval (-75071932864 / 1000000000000) (-75071932863 / 1000000000000))
    | 4 => (orderedInterval (-16556752044 / 1000000000000) (-16556751799 / 1000000000000), orderedInterval (54928924220 / 1000000000000) (54928924464 / 1000000000000))
    | 5 => (orderedInterval (-30460016525 / 1000000000000) (-30459915913 / 1000000000000), orderedInterval (16840844386 / 1000000000000) (16840944998 / 1000000000000))
    | 6 => (orderedInterval (-39726297884 / 1000000000000) (-39726295058 / 1000000000000), orderedInterval (8121296412 / 1000000000000) (8121299237 / 1000000000000))
    | 7 => (orderedInterval (-30580694583 / 1000000000000) (-30580686631 / 1000000000000), orderedInterval (4906247642 / 1000000000000) (4906255594 / 1000000000000))
    | 8 => (orderedInterval (-11914586900 / 1000000000000) (-11914586844 / 1000000000000), orderedInterval (34071139433 / 1000000000000) (34071139489 / 1000000000000))
    | 9 => (orderedInterval (-4220519337 / 1000000000000) (-4220519336 / 1000000000000), orderedInterval (-28820555280 / 1000000000000) (-28820555279 / 1000000000000))
    | 10 => (orderedInterval (14005145724 / 1000000000000) (14005145725 / 1000000000000), orderedInterval (35672394737 / 1000000000000) (35672394738 / 1000000000000))
    | 11 => (orderedInterval (8795949993 / 1000000000000) (8795949998 / 1000000000000), orderedInterval (-27408684957 / 1000000000000) (-27408684952 / 1000000000000))
    | 12 => (orderedInterval (14766737582 / 1000000000000) (14766737726 / 1000000000000), orderedInterval (-25864716035 / 1000000000000) (-25864715891 / 1000000000000))
    | 13 => (orderedInterval (-32724009292 / 1000000000000) (-32724009290 / 1000000000000), orderedInterval (-13058556687 / 1000000000000) (-13058556685 / 1000000000000))
    | 14 => (orderedInterval (-21160131492 / 1000000000000) (-21160131491 / 1000000000000), orderedInterval (-25433427887 / 1000000000000) (-25433427886 / 1000000000000))
    | 15 => (orderedInterval (35954554294 / 1000000000000) (35954554381 / 1000000000000), orderedInterval (4582635351 / 1000000000000) (4582635438 / 1000000000000))
    | 16 => (orderedInterval (38565110051 / 1000000000000) (38565110364 / 1000000000000), orderedInterval (125315475 / 1000000000000) (125315789 / 1000000000000))
    | 17 => (orderedInterval (-25867984236 / 1000000000000) (-25867956347 / 1000000000000), orderedInterval (18918996341 / 1000000000000) (18919024230 / 1000000000000))
    | 18 => (orderedInterval (-43001127581 / 1000000000000) (-43001127495 / 1000000000000), orderedInterval (-2398686600 / 1000000000000) (-2398686515 / 1000000000000))
    | 19 => (orderedInterval (21633998810 / 1000000000000) (21634000175 / 1000000000000), orderedInterval (-41514923828 / 1000000000000) (-41514922463 / 1000000000000))
    | 20 => (orderedInterval (33661646048 / 1000000000000) (33661646049 / 1000000000000), orderedInterval (48530282103 / 1000000000000) (48530282104 / 1000000000000))
    | 21 => (orderedInterval (-77544220913 / 1000000000000) (-77544220911 / 1000000000000), orderedInterval (-21733266725 / 1000000000000) (-21733266724 / 1000000000000))
    | 22 => (orderedInterval (20763494462 / 1000000000000) (20763495421 / 1000000000000), orderedInterval (-44354714937 / 1000000000000) (-44354713978 / 1000000000000))
    | 23 => (orderedInterval (-26844068475 / 1000000000000) (-26844059123 / 1000000000000), orderedInterval (32184150800 / 1000000000000) (32184160151 / 1000000000000))
    | 24 => (orderedInterval (-19852500077 / 1000000000000) (-19852500076 / 1000000000000), orderedInterval (-61206468024 / 1000000000000) (-61206468023 / 1000000000000))
    | 25 => (orderedInterval (16907638158 / 1000000000000) (16907638607 / 1000000000000), orderedInterval (-27117562016 / 1000000000000) (-27117561566 / 1000000000000))
    | _ => (orderedInterval (13568803727 / 1000000000000) (13568803849 / 1000000000000), orderedInterval (-36672552898 / 1000000000000) (-36672552775 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4490704650 / 1000000000000) (-4490704623 / 1000000000000)
      | 1 => orderedInterval (2168248108 / 1000000000000) (2168255310 / 1000000000000)
      | 2 => orderedInterval (655278661 / 1000000000000) (655278927 / 1000000000000)
      | 3 => orderedInterval (3037997428 / 1000000000000) (3037997562 / 1000000000000)
      | 4 => orderedInterval (-3253978858 / 1000000000000) (-3253978815 / 1000000000000)
      | 5 => orderedInterval (-2454084378 / 1000000000000) (-2454083612 / 1000000000000)
      | 6 => orderedInterval (6746935793 / 1000000000000) (6746935969 / 1000000000000)
      | 7 => orderedInterval (3018102894 / 1000000000000) (3018103673 / 1000000000000)
      | _ => orderedInterval (-4041856798 / 1000000000000) (-4041856645 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17959130591 / 1000000000000) (-17959130562 / 1000000000000)
      | 1 => orderedInterval (-543812436 / 1000000000000) (-543801172 / 1000000000000)
      | 2 => orderedInterval (900673888 / 1000000000000) (900674409 / 1000000000000)
      | 3 => orderedInterval (5937169293 / 1000000000000) (5937169570 / 1000000000000)
      | 4 => orderedInterval (-663886335 / 1000000000000) (-663886264 / 1000000000000)
      | 5 => orderedInterval (962880769 / 1000000000000) (962882161 / 1000000000000)
      | 6 => orderedInterval (3286905080 / 1000000000000) (3286905239 / 1000000000000)
      | 7 => orderedInterval (-1753967947 / 1000000000000) (-1753967118 / 1000000000000)
      | _ => orderedInterval (12481637501 / 1000000000000) (12481637729 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (5565558919 / 1000000000000) (5565558953 / 1000000000000)
      | 1 => orderedInterval (-5146225569 / 1000000000000) (-5146207892 / 1000000000000)
      | 2 => orderedInterval (-3083659188 / 1000000000000) (-3083658165 / 1000000000000)
      | 3 => orderedInterval (-12059130169 / 1000000000000) (-12059129573 / 1000000000000)
      | 4 => orderedInterval (8122541213 / 1000000000000) (8122541333 / 1000000000000)
      | 5 => orderedInterval (4987827749 / 1000000000000) (4987830295 / 1000000000000)
      | 6 => orderedInterval (-6605012312 / 1000000000000) (-6605012164 / 1000000000000)
      | 7 => orderedInterval (-2228636728 / 1000000000000) (-2228635837 / 1000000000000)
      | _ => orderedInterval (8673521970 / 1000000000000) (8673522325 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18005303391 / 1000000000000) (18005303430 / 1000000000000)
      | 1 => orderedInterval (4233297819 / 1000000000000) (4233325522 / 1000000000000)
      | 2 => orderedInterval (-1367731698 / 1000000000000) (-1367729685 / 1000000000000)
      | 3 => orderedInterval (-16060730814 / 1000000000000) (-16060729509 / 1000000000000)
      | 4 => orderedInterval (-870733378 / 1000000000000) (-870733169 / 1000000000000)
      | 5 => orderedInterval (-3220948734 / 1000000000000) (-3220944066 / 1000000000000)
      | 6 => orderedInterval (-2174789140 / 1000000000000) (-2174789003 / 1000000000000)
      | 7 => orderedInterval (2618919613 / 1000000000000) (2618920572 / 1000000000000)
      | _ => orderedInterval (-27364148477 / 1000000000000) (-27364147900 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-7016924810 / 1000000000000) (-7016924765 / 1000000000000)
      | 1 => orderedInterval (12985490454 / 1000000000000) (12985533959 / 1000000000000)
      | 2 => orderedInterval (13164984091 / 1000000000000) (13164988064 / 1000000000000)
      | 3 => orderedInterval (56166673338 / 1000000000000) (56166676236 / 1000000000000)
      | 4 => orderedInterval (-21474410466 / 1000000000000) (-21474410094 / 1000000000000)
      | 5 => orderedInterval (-11762725525 / 1000000000000) (-11762716932 / 1000000000000)
      | 6 => orderedInterval (6941271612 / 1000000000000) (6941271742 / 1000000000000)
      | 7 => orderedInterval (2626776893 / 1000000000000) (2626777927 / 1000000000000)
      | _ => orderedInterval (-22352168974 / 1000000000000) (-22352168004 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (1385938200 / 1000000000000) (1385947746 / 1000000000000)
    | 1 => orderedInterval (2648469222 / 1000000000000) (2648483992 / 1000000000000)
    | 2 => orderedInterval (-1773214115 / 1000000000000) (-1773190725 / 1000000000000)
    | 3 => orderedInterval (-26201561418 / 1000000000000) (-26201523808 / 1000000000000)
    | _ => orderedInterval (29278966613 / 1000000000000) (29279028133 / 1000000000000)

theorem compactCertificate464_stateChecks0 :
    compactCertificate464.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (671 / 2)) (orderedInterval (-5846067571 / 1000000000000) (-5846067569 / 1000000000000), orderedInterval (-43157836256 / 1000000000000) (-43157836255 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (988511126041571 / 4000000000000)) (orderedInterval (13691765680 / 1000000000000) (13691765810 / 1000000000000), orderedInterval (-48901164376 / 1000000000000) (-48901164246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (319664187919043 / 800000000000)) (orderedInterval (-39213771246 / 1000000000000) (-39213771227 / 1000000000000), orderedInterval (-7400787936 / 1000000000000) (-7400787917 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks1 :
    compactCertificate464.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (288445081197097 / 4000000000000)) (orderedInterval (-55983341774 / 1000000000000) (-55983341773 / 1000000000000), orderedInterval (-75071932864 / 1000000000000) (-75071932863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (774804061252309 / 4000000000000)) (orderedInterval (-16556752044 / 1000000000000) (-16556751799 / 1000000000000), orderedInterval (54928924220 / 1000000000000) (54928924464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2103743747154753 / 4000000000000)) (orderedInterval (-30460016525 / 1000000000000) (-30459915913 / 1000000000000), orderedInterval (16840844386 / 1000000000000) (16840944998 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks2 :
    compactCertificate464.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1549608122505289 / 4000000000000)) (orderedInterval (-39726297884 / 1000000000000) (-39726295058 / 1000000000000), orderedInterval (8121296412 / 1000000000000) (8121299237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2655279930137197 / 4000000000000)) (orderedInterval (-30580694583 / 1000000000000) (-30580686631 / 1000000000000), orderedInterval (4906247642 / 1000000000000) (4906255594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1955867178609223 / 4000000000000)) (orderedInterval (-11914586900 / 1000000000000) (-11914586844 / 1000000000000), orderedInterval (34071139433 / 1000000000000) (34071139489 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks3 :
    compactCertificate464.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3000803225804329 / 4000000000000)) (orderedInterval (-4220519337 / 1000000000000) (-4220519336 / 1000000000000), orderedInterval (-28820555280 / 1000000000000) (-28820555279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1732514550203041 / 4000000000000)) (orderedInterval (14005145724 / 1000000000000) (14005145725 / 1000000000000), orderedInterval (35672394737 / 1000000000000) (35672394738 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3074377472061269 / 4000000000000)) (orderedInterval (8795949993 / 1000000000000) (8795949998 / 1000000000000), orderedInterval (-27408684957 / 1000000000000) (-27408684952 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks4 :
    compactCertificate464.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2872482232156361 / 4000000000000)) (orderedInterval (14766737582 / 1000000000000) (14766737726 / 1000000000000), orderedInterval (-25864716035 / 1000000000000) (-25864715891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2049938860876313 / 4000000000000)) (orderedInterval (-32724009292 / 1000000000000) (-32724009290 / 1000000000000), orderedInterval (-13058556687 / 1000000000000) (-13058556685 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2324412183756927 / 4000000000000)) (orderedInterval (-21160131492 / 1000000000000) (-21160131491 / 1000000000000), orderedInterval (-25433427887 / 1000000000000) (-25433427886 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks5 :
    compactCertificate464.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1937852546664463 / 4000000000000)) (orderedInterval (35954554294 / 1000000000000) (35954554381 / 1000000000000), orderedInterval (4582635351 / 1000000000000) (4582635438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1712151494149723 / 4000000000000)) (orderedInterval (38565110051 / 1000000000000) (38565110364 / 1000000000000), orderedInterval (125315475 / 1000000000000) (125315789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (496248237314577 / 800000000000)) (orderedInterval (-25867984236 / 1000000000000) (-25867956347 / 1000000000000), orderedInterval (18918996341 / 1000000000000) (18919024230 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks6 :
    compactCertificate464.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1372648740526019 / 4000000000000)) (orderedInterval (-43001127581 / 1000000000000) (-43001127495 / 1000000000000), orderedInterval (-2398686600 / 1000000000000) (-2398686515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1163609539012459 / 4000000000000)) (orderedInterval (21633998810 / 1000000000000) (21634000175 / 1000000000000), orderedInterval (-41514923828 / 1000000000000) (-41514922463 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (728132821390777 / 4000000000000)) (orderedInterval (33661646048 / 1000000000000) (33661646049 / 1000000000000), orderedInterval (48530282103 / 1000000000000) (48530282104 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks7 :
    compactCertificate464.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (391592253004359 / 4000000000000)) (orderedInterval (-77544220913 / 1000000000000) (-77544220911 / 1000000000000), orderedInterval (-21733266725 / 1000000000000) (-21733266724 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1063249142450077 / 4000000000000)) (orderedInterval (20763494462 / 1000000000000) (20763495421 / 1000000000000), orderedInterval (-44354714937 / 1000000000000) (-44354713978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1451775804050429 / 4000000000000)) (orderedInterval (-26844068475 / 1000000000000) (-26844059123 / 1000000000000), orderedInterval (32184150800 / 1000000000000) (32184160151 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_stateChecks8 :
    compactCertificate464.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (613867178609223 / 4000000000000)) (orderedInterval (-19852500077 / 1000000000000) (-19852500076 / 1000000000000), orderedInterval (-61206468024 / 1000000000000) (-61206468023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2495336000159783 / 4000000000000)) (orderedInterval (16907638158 / 1000000000000) (16907638607 / 1000000000000), orderedInterval (-27117562016 / 1000000000000) (-27117561566 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1666768804096297 / 4000000000000)) (orderedInterval (13568803727 / 1000000000000) (13568803849 / 1000000000000), orderedInterval (-36672552898 / 1000000000000) (-36672552775 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_states : ∀ j,
    BesselStateValid (compactCertificate464.point j) (compactCertificate464.state j) :=
  compactCertificate464.statesValid_of_checks3 compactCertificate464_stateChecks0
    compactCertificate464_stateChecks1 compactCertificate464_stateChecks2
    compactCertificate464_stateChecks3 compactCertificate464_stateChecks4
    compactCertificate464_stateChecks5 compactCertificate464_stateChecks6
    compactCertificate464_stateChecks7 compactCertificate464_stateChecks8

theorem compactCertificate464_chunkChecks0_0 :
    compactCertificate464.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (671 / 2) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5846067571 / 1000000000000) (-5846067569 / 1000000000000), orderedInterval (-43157836256 / 1000000000000) (-43157836255 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (988511126041571 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13691765680 / 1000000000000) (13691765810 / 1000000000000), orderedInterval (-48901164376 / 1000000000000) (-48901164246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (319664187919043 / 800000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39213771246 / 1000000000000) (-39213771227 / 1000000000000), orderedInterval (-7400787936 / 1000000000000) (-7400787917 / 1000000000000)))) (orderedInterval (-4490704650 / 1000000000000) (-4490704623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (288445081197097 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55983341774 / 1000000000000) (-55983341773 / 1000000000000), orderedInterval (-75071932864 / 1000000000000) (-75071932863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (774804061252309 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16556752044 / 1000000000000) (-16556751799 / 1000000000000), orderedInterval (54928924220 / 1000000000000) (54928924464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2103743747154753 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30460016525 / 1000000000000) (-30459915913 / 1000000000000), orderedInterval (16840844386 / 1000000000000) (16840944998 / 1000000000000)))) (orderedInterval (2168248108 / 1000000000000) (2168255310 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1549608122505289 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39726297884 / 1000000000000) (-39726295058 / 1000000000000), orderedInterval (8121296412 / 1000000000000) (8121299237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2655279930137197 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30580694583 / 1000000000000) (-30580686631 / 1000000000000), orderedInterval (4906247642 / 1000000000000) (4906255594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1955867178609223 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11914586900 / 1000000000000) (-11914586844 / 1000000000000), orderedInterval (34071139433 / 1000000000000) (34071139489 / 1000000000000)))) (orderedInterval (655278661 / 1000000000000) (655278927 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks0_1 :
    compactCertificate464.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3000803225804329 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4220519337 / 1000000000000) (-4220519336 / 1000000000000), orderedInterval (-28820555280 / 1000000000000) (-28820555279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1732514550203041 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14005145724 / 1000000000000) (14005145725 / 1000000000000), orderedInterval (35672394737 / 1000000000000) (35672394738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3074377472061269 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8795949993 / 1000000000000) (8795949998 / 1000000000000), orderedInterval (-27408684957 / 1000000000000) (-27408684952 / 1000000000000)))) (orderedInterval (3037997428 / 1000000000000) (3037997562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2872482232156361 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14766737582 / 1000000000000) (14766737726 / 1000000000000), orderedInterval (-25864716035 / 1000000000000) (-25864715891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2049938860876313 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32724009292 / 1000000000000) (-32724009290 / 1000000000000), orderedInterval (-13058556687 / 1000000000000) (-13058556685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2324412183756927 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21160131492 / 1000000000000) (-21160131491 / 1000000000000), orderedInterval (-25433427887 / 1000000000000) (-25433427886 / 1000000000000)))) (orderedInterval (-3253978858 / 1000000000000) (-3253978815 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1937852546664463 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35954554294 / 1000000000000) (35954554381 / 1000000000000), orderedInterval (4582635351 / 1000000000000) (4582635438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1712151494149723 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38565110051 / 1000000000000) (38565110364 / 1000000000000), orderedInterval (125315475 / 1000000000000) (125315789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (496248237314577 / 800000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25867984236 / 1000000000000) (-25867956347 / 1000000000000), orderedInterval (18918996341 / 1000000000000) (18919024230 / 1000000000000)))) (orderedInterval (-2454084378 / 1000000000000) (-2454083612 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks0_2 :
    compactCertificate464.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1372648740526019 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43001127581 / 1000000000000) (-43001127495 / 1000000000000), orderedInterval (-2398686600 / 1000000000000) (-2398686515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1163609539012459 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21633998810 / 1000000000000) (21634000175 / 1000000000000), orderedInterval (-41514923828 / 1000000000000) (-41514922463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (728132821390777 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33661646048 / 1000000000000) (33661646049 / 1000000000000), orderedInterval (48530282103 / 1000000000000) (48530282104 / 1000000000000)))) (orderedInterval (6746935793 / 1000000000000) (6746935969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (391592253004359 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77544220913 / 1000000000000) (-77544220911 / 1000000000000), orderedInterval (-21733266725 / 1000000000000) (-21733266724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1063249142450077 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20763494462 / 1000000000000) (20763495421 / 1000000000000), orderedInterval (-44354714937 / 1000000000000) (-44354713978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1451775804050429 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26844068475 / 1000000000000) (-26844059123 / 1000000000000), orderedInterval (32184150800 / 1000000000000) (32184160151 / 1000000000000)))) (orderedInterval (3018102894 / 1000000000000) (3018103673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (613867178609223 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19852500077 / 1000000000000) (-19852500076 / 1000000000000), orderedInterval (-61206468024 / 1000000000000) (-61206468023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2495336000159783 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16907638158 / 1000000000000) (16907638607 / 1000000000000), orderedInterval (-27117562016 / 1000000000000) (-27117561566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1666768804096297 / 4000000000000) 0 (IntervalRat.scale (671 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13568803727 / 1000000000000) (13568803849 / 1000000000000), orderedInterval (-36672552898 / 1000000000000) (-36672552775 / 1000000000000)))) (orderedInterval (-4041856798 / 1000000000000) (-4041856645 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks0 :
    compactCertificate464.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate464.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate464_chunkChecks0_0
    compactCertificate464_chunkChecks0_1 compactCertificate464_chunkChecks0_2

theorem compactCertificate464_chunkChecks1_0 :
    compactCertificate464.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (671 / 2) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5846067571 / 1000000000000) (-5846067569 / 1000000000000), orderedInterval (-43157836256 / 1000000000000) (-43157836255 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (988511126041571 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13691765680 / 1000000000000) (13691765810 / 1000000000000), orderedInterval (-48901164376 / 1000000000000) (-48901164246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (319664187919043 / 800000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39213771246 / 1000000000000) (-39213771227 / 1000000000000), orderedInterval (-7400787936 / 1000000000000) (-7400787917 / 1000000000000)))) (orderedInterval (-17959130591 / 1000000000000) (-17959130562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (288445081197097 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55983341774 / 1000000000000) (-55983341773 / 1000000000000), orderedInterval (-75071932864 / 1000000000000) (-75071932863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (774804061252309 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16556752044 / 1000000000000) (-16556751799 / 1000000000000), orderedInterval (54928924220 / 1000000000000) (54928924464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2103743747154753 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30460016525 / 1000000000000) (-30459915913 / 1000000000000), orderedInterval (16840844386 / 1000000000000) (16840944998 / 1000000000000)))) (orderedInterval (-543812436 / 1000000000000) (-543801172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1549608122505289 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39726297884 / 1000000000000) (-39726295058 / 1000000000000), orderedInterval (8121296412 / 1000000000000) (8121299237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2655279930137197 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30580694583 / 1000000000000) (-30580686631 / 1000000000000), orderedInterval (4906247642 / 1000000000000) (4906255594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1955867178609223 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11914586900 / 1000000000000) (-11914586844 / 1000000000000), orderedInterval (34071139433 / 1000000000000) (34071139489 / 1000000000000)))) (orderedInterval (900673888 / 1000000000000) (900674409 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks1_1 :
    compactCertificate464.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3000803225804329 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4220519337 / 1000000000000) (-4220519336 / 1000000000000), orderedInterval (-28820555280 / 1000000000000) (-28820555279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1732514550203041 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14005145724 / 1000000000000) (14005145725 / 1000000000000), orderedInterval (35672394737 / 1000000000000) (35672394738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3074377472061269 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8795949993 / 1000000000000) (8795949998 / 1000000000000), orderedInterval (-27408684957 / 1000000000000) (-27408684952 / 1000000000000)))) (orderedInterval (5937169293 / 1000000000000) (5937169570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2872482232156361 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14766737582 / 1000000000000) (14766737726 / 1000000000000), orderedInterval (-25864716035 / 1000000000000) (-25864715891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2049938860876313 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32724009292 / 1000000000000) (-32724009290 / 1000000000000), orderedInterval (-13058556687 / 1000000000000) (-13058556685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2324412183756927 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21160131492 / 1000000000000) (-21160131491 / 1000000000000), orderedInterval (-25433427887 / 1000000000000) (-25433427886 / 1000000000000)))) (orderedInterval (-663886335 / 1000000000000) (-663886264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1937852546664463 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35954554294 / 1000000000000) (35954554381 / 1000000000000), orderedInterval (4582635351 / 1000000000000) (4582635438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1712151494149723 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38565110051 / 1000000000000) (38565110364 / 1000000000000), orderedInterval (125315475 / 1000000000000) (125315789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (496248237314577 / 800000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25867984236 / 1000000000000) (-25867956347 / 1000000000000), orderedInterval (18918996341 / 1000000000000) (18919024230 / 1000000000000)))) (orderedInterval (962880769 / 1000000000000) (962882161 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks1_2 :
    compactCertificate464.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1372648740526019 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43001127581 / 1000000000000) (-43001127495 / 1000000000000), orderedInterval (-2398686600 / 1000000000000) (-2398686515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1163609539012459 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21633998810 / 1000000000000) (21634000175 / 1000000000000), orderedInterval (-41514923828 / 1000000000000) (-41514922463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (728132821390777 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33661646048 / 1000000000000) (33661646049 / 1000000000000), orderedInterval (48530282103 / 1000000000000) (48530282104 / 1000000000000)))) (orderedInterval (3286905080 / 1000000000000) (3286905239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (391592253004359 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77544220913 / 1000000000000) (-77544220911 / 1000000000000), orderedInterval (-21733266725 / 1000000000000) (-21733266724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1063249142450077 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20763494462 / 1000000000000) (20763495421 / 1000000000000), orderedInterval (-44354714937 / 1000000000000) (-44354713978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1451775804050429 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26844068475 / 1000000000000) (-26844059123 / 1000000000000), orderedInterval (32184150800 / 1000000000000) (32184160151 / 1000000000000)))) (orderedInterval (-1753967947 / 1000000000000) (-1753967118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (613867178609223 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19852500077 / 1000000000000) (-19852500076 / 1000000000000), orderedInterval (-61206468024 / 1000000000000) (-61206468023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2495336000159783 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16907638158 / 1000000000000) (16907638607 / 1000000000000), orderedInterval (-27117562016 / 1000000000000) (-27117561566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1666768804096297 / 4000000000000) 1 (IntervalRat.scale (671 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13568803727 / 1000000000000) (13568803849 / 1000000000000), orderedInterval (-36672552898 / 1000000000000) (-36672552775 / 1000000000000)))) (orderedInterval (12481637501 / 1000000000000) (12481637729 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks1 :
    compactCertificate464.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate464.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate464_chunkChecks1_0
    compactCertificate464_chunkChecks1_1 compactCertificate464_chunkChecks1_2

theorem compactCertificate464_chunkChecks2_0 :
    compactCertificate464.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (671 / 2) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5846067571 / 1000000000000) (-5846067569 / 1000000000000), orderedInterval (-43157836256 / 1000000000000) (-43157836255 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (988511126041571 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13691765680 / 1000000000000) (13691765810 / 1000000000000), orderedInterval (-48901164376 / 1000000000000) (-48901164246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (319664187919043 / 800000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39213771246 / 1000000000000) (-39213771227 / 1000000000000), orderedInterval (-7400787936 / 1000000000000) (-7400787917 / 1000000000000)))) (orderedInterval (5565558919 / 1000000000000) (5565558953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (288445081197097 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55983341774 / 1000000000000) (-55983341773 / 1000000000000), orderedInterval (-75071932864 / 1000000000000) (-75071932863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (774804061252309 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16556752044 / 1000000000000) (-16556751799 / 1000000000000), orderedInterval (54928924220 / 1000000000000) (54928924464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2103743747154753 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30460016525 / 1000000000000) (-30459915913 / 1000000000000), orderedInterval (16840844386 / 1000000000000) (16840944998 / 1000000000000)))) (orderedInterval (-5146225569 / 1000000000000) (-5146207892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1549608122505289 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39726297884 / 1000000000000) (-39726295058 / 1000000000000), orderedInterval (8121296412 / 1000000000000) (8121299237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2655279930137197 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30580694583 / 1000000000000) (-30580686631 / 1000000000000), orderedInterval (4906247642 / 1000000000000) (4906255594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1955867178609223 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11914586900 / 1000000000000) (-11914586844 / 1000000000000), orderedInterval (34071139433 / 1000000000000) (34071139489 / 1000000000000)))) (orderedInterval (-3083659188 / 1000000000000) (-3083658165 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks2_1 :
    compactCertificate464.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3000803225804329 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4220519337 / 1000000000000) (-4220519336 / 1000000000000), orderedInterval (-28820555280 / 1000000000000) (-28820555279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1732514550203041 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14005145724 / 1000000000000) (14005145725 / 1000000000000), orderedInterval (35672394737 / 1000000000000) (35672394738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3074377472061269 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8795949993 / 1000000000000) (8795949998 / 1000000000000), orderedInterval (-27408684957 / 1000000000000) (-27408684952 / 1000000000000)))) (orderedInterval (-12059130169 / 1000000000000) (-12059129573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2872482232156361 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14766737582 / 1000000000000) (14766737726 / 1000000000000), orderedInterval (-25864716035 / 1000000000000) (-25864715891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2049938860876313 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32724009292 / 1000000000000) (-32724009290 / 1000000000000), orderedInterval (-13058556687 / 1000000000000) (-13058556685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2324412183756927 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21160131492 / 1000000000000) (-21160131491 / 1000000000000), orderedInterval (-25433427887 / 1000000000000) (-25433427886 / 1000000000000)))) (orderedInterval (8122541213 / 1000000000000) (8122541333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1937852546664463 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35954554294 / 1000000000000) (35954554381 / 1000000000000), orderedInterval (4582635351 / 1000000000000) (4582635438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1712151494149723 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38565110051 / 1000000000000) (38565110364 / 1000000000000), orderedInterval (125315475 / 1000000000000) (125315789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (496248237314577 / 800000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25867984236 / 1000000000000) (-25867956347 / 1000000000000), orderedInterval (18918996341 / 1000000000000) (18919024230 / 1000000000000)))) (orderedInterval (4987827749 / 1000000000000) (4987830295 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks2_2 :
    compactCertificate464.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1372648740526019 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43001127581 / 1000000000000) (-43001127495 / 1000000000000), orderedInterval (-2398686600 / 1000000000000) (-2398686515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1163609539012459 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21633998810 / 1000000000000) (21634000175 / 1000000000000), orderedInterval (-41514923828 / 1000000000000) (-41514922463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (728132821390777 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33661646048 / 1000000000000) (33661646049 / 1000000000000), orderedInterval (48530282103 / 1000000000000) (48530282104 / 1000000000000)))) (orderedInterval (-6605012312 / 1000000000000) (-6605012164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (391592253004359 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77544220913 / 1000000000000) (-77544220911 / 1000000000000), orderedInterval (-21733266725 / 1000000000000) (-21733266724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1063249142450077 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20763494462 / 1000000000000) (20763495421 / 1000000000000), orderedInterval (-44354714937 / 1000000000000) (-44354713978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1451775804050429 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26844068475 / 1000000000000) (-26844059123 / 1000000000000), orderedInterval (32184150800 / 1000000000000) (32184160151 / 1000000000000)))) (orderedInterval (-2228636728 / 1000000000000) (-2228635837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (613867178609223 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19852500077 / 1000000000000) (-19852500076 / 1000000000000), orderedInterval (-61206468024 / 1000000000000) (-61206468023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2495336000159783 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16907638158 / 1000000000000) (16907638607 / 1000000000000), orderedInterval (-27117562016 / 1000000000000) (-27117561566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1666768804096297 / 4000000000000) 2 (IntervalRat.scale (671 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13568803727 / 1000000000000) (13568803849 / 1000000000000), orderedInterval (-36672552898 / 1000000000000) (-36672552775 / 1000000000000)))) (orderedInterval (8673521970 / 1000000000000) (8673522325 / 1000000000000))) = true
  rfl'

theorem compactCertificate464_chunkChecks2 :
    compactCertificate464.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate464.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate464_chunkChecks2_0
    compactCertificate464_chunkChecks2_1 compactCertificate464_chunkChecks2_2

theorem compactCertificate464_chunkChecks3_0 :
    compactCertificate464.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (671 / 2) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5846067571 / 1000000000000) (-5846067569 / 1000000000000), orderedInterval (-43157836256 / 1000000000000) (-43157836255 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (988511126041571 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13691765680 / 1000000000000) (13691765810 / 1000000000000), orderedInterval (-48901164376 / 1000000000000) (-48901164246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (319664187919043 / 800000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39213771246 / 1000000000000) (-39213771227 / 1000000000000), orderedInterval (-7400787936 / 1000000000000) (-7400787917 / 1000000000000)))) (orderedInterval (18005303391 / 1000000000000) (18005303430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (288445081197097 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55983341774 / 1000000000000) (-55983341773 / 1000000000000), orderedInterval (-75071932864 / 1000000000000) (-75071932863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (774804061252309 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16556752044 / 1000000000000) (-16556751799 / 1000000000000), orderedInterval (54928924220 / 1000000000000) (54928924464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2103743747154753 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30460016525 / 1000000000000) (-30459915913 / 1000000000000), orderedInterval (16840844386 / 1000000000000) (16840944998 / 1000000000000)))) (orderedInterval (4233297819 / 1000000000000) (4233325522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1549608122505289 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39726297884 / 1000000000000) (-39726295058 / 1000000000000), orderedInterval (8121296412 / 1000000000000) (8121299237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2655279930137197 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30580694583 / 1000000000000) (-30580686631 / 1000000000000), orderedInterval (4906247642 / 1000000000000) (4906255594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1955867178609223 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11914586900 / 1000000000000) (-11914586844 / 1000000000000), orderedInterval (34071139433 / 1000000000000) (34071139489 / 1000000000000)))) (orderedInterval (-1367731698 / 1000000000000) (-1367729685 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate464_chunkChecks3_1 :
    compactCertificate464.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3000803225804329 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4220519337 / 1000000000000) (-4220519336 / 1000000000000), orderedInterval (-28820555280 / 1000000000000) (-28820555279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1732514550203041 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14005145724 / 1000000000000) (14005145725 / 1000000000000), orderedInterval (35672394737 / 1000000000000) (35672394738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3074377472061269 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8795949993 / 1000000000000) (8795949998 / 1000000000000), orderedInterval (-27408684957 / 1000000000000) (-27408684952 / 1000000000000)))) (orderedInterval (-16060730814 / 1000000000000) (-16060729509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2872482232156361 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14766737582 / 1000000000000) (14766737726 / 1000000000000), orderedInterval (-25864716035 / 1000000000000) (-25864715891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2049938860876313 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32724009292 / 1000000000000) (-32724009290 / 1000000000000), orderedInterval (-13058556687 / 1000000000000) (-13058556685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2324412183756927 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21160131492 / 1000000000000) (-21160131491 / 1000000000000), orderedInterval (-25433427887 / 1000000000000) (-25433427886 / 1000000000000)))) (orderedInterval (-870733378 / 1000000000000) (-870733169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1937852546664463 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35954554294 / 1000000000000) (35954554381 / 1000000000000), orderedInterval (4582635351 / 1000000000000) (4582635438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1712151494149723 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38565110051 / 1000000000000) (38565110364 / 1000000000000), orderedInterval (125315475 / 1000000000000) (125315789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (496248237314577 / 800000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25867984236 / 1000000000000) (-25867956347 / 1000000000000), orderedInterval (18918996341 / 1000000000000) (18919024230 / 1000000000000)))) (orderedInterval (-3220948734 / 1000000000000) (-3220944066 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate464_chunkChecks3_2 :
    compactCertificate464.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1372648740526019 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43001127581 / 1000000000000) (-43001127495 / 1000000000000), orderedInterval (-2398686600 / 1000000000000) (-2398686515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1163609539012459 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21633998810 / 1000000000000) (21634000175 / 1000000000000), orderedInterval (-41514923828 / 1000000000000) (-41514922463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (728132821390777 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33661646048 / 1000000000000) (33661646049 / 1000000000000), orderedInterval (48530282103 / 1000000000000) (48530282104 / 1000000000000)))) (orderedInterval (-2174789140 / 1000000000000) (-2174789003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (391592253004359 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77544220913 / 1000000000000) (-77544220911 / 1000000000000), orderedInterval (-21733266725 / 1000000000000) (-21733266724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1063249142450077 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20763494462 / 1000000000000) (20763495421 / 1000000000000), orderedInterval (-44354714937 / 1000000000000) (-44354713978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1451775804050429 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26844068475 / 1000000000000) (-26844059123 / 1000000000000), orderedInterval (32184150800 / 1000000000000) (32184160151 / 1000000000000)))) (orderedInterval (2618919613 / 1000000000000) (2618920572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (613867178609223 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19852500077 / 1000000000000) (-19852500076 / 1000000000000), orderedInterval (-61206468024 / 1000000000000) (-61206468023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2495336000159783 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16907638158 / 1000000000000) (16907638607 / 1000000000000), orderedInterval (-27117562016 / 1000000000000) (-27117561566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1666768804096297 / 4000000000000) 3 (IntervalRat.scale (671 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13568803727 / 1000000000000) (13568803849 / 1000000000000), orderedInterval (-36672552898 / 1000000000000) (-36672552775 / 1000000000000)))) (orderedInterval (-27364148477 / 1000000000000) (-27364147900 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate464_chunkChecks3 :
    compactCertificate464.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate464.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate464_chunkChecks3_0
    compactCertificate464_chunkChecks3_1 compactCertificate464_chunkChecks3_2

theorem compactCertificate464_chunkChecks4_0 :
    compactCertificate464.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (671 / 2) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5846067571 / 1000000000000) (-5846067569 / 1000000000000), orderedInterval (-43157836256 / 1000000000000) (-43157836255 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (988511126041571 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (13691765680 / 1000000000000) (13691765810 / 1000000000000), orderedInterval (-48901164376 / 1000000000000) (-48901164246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (319664187919043 / 800000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39213771246 / 1000000000000) (-39213771227 / 1000000000000), orderedInterval (-7400787936 / 1000000000000) (-7400787917 / 1000000000000)))) (orderedInterval (-7016924810 / 1000000000000) (-7016924765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (288445081197097 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-55983341774 / 1000000000000) (-55983341773 / 1000000000000), orderedInterval (-75071932864 / 1000000000000) (-75071932863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (774804061252309 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16556752044 / 1000000000000) (-16556751799 / 1000000000000), orderedInterval (54928924220 / 1000000000000) (54928924464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2103743747154753 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30460016525 / 1000000000000) (-30459915913 / 1000000000000), orderedInterval (16840844386 / 1000000000000) (16840944998 / 1000000000000)))) (orderedInterval (12985490454 / 1000000000000) (12985533959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1549608122505289 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39726297884 / 1000000000000) (-39726295058 / 1000000000000), orderedInterval (8121296412 / 1000000000000) (8121299237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2655279930137197 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30580694583 / 1000000000000) (-30580686631 / 1000000000000), orderedInterval (4906247642 / 1000000000000) (4906255594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1955867178609223 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-11914586900 / 1000000000000) (-11914586844 / 1000000000000), orderedInterval (34071139433 / 1000000000000) (34071139489 / 1000000000000)))) (orderedInterval (13164984091 / 1000000000000) (13164988064 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate464_chunkChecks4_1 :
    compactCertificate464.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3000803225804329 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-4220519337 / 1000000000000) (-4220519336 / 1000000000000), orderedInterval (-28820555280 / 1000000000000) (-28820555279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1732514550203041 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14005145724 / 1000000000000) (14005145725 / 1000000000000), orderedInterval (35672394737 / 1000000000000) (35672394738 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3074377472061269 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8795949993 / 1000000000000) (8795949998 / 1000000000000), orderedInterval (-27408684957 / 1000000000000) (-27408684952 / 1000000000000)))) (orderedInterval (56166673338 / 1000000000000) (56166676236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2872482232156361 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14766737582 / 1000000000000) (14766737726 / 1000000000000), orderedInterval (-25864716035 / 1000000000000) (-25864715891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2049938860876313 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32724009292 / 1000000000000) (-32724009290 / 1000000000000), orderedInterval (-13058556687 / 1000000000000) (-13058556685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2324412183756927 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21160131492 / 1000000000000) (-21160131491 / 1000000000000), orderedInterval (-25433427887 / 1000000000000) (-25433427886 / 1000000000000)))) (orderedInterval (-21474410466 / 1000000000000) (-21474410094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1937852546664463 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35954554294 / 1000000000000) (35954554381 / 1000000000000), orderedInterval (4582635351 / 1000000000000) (4582635438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1712151494149723 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38565110051 / 1000000000000) (38565110364 / 1000000000000), orderedInterval (125315475 / 1000000000000) (125315789 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (496248237314577 / 800000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25867984236 / 1000000000000) (-25867956347 / 1000000000000), orderedInterval (18918996341 / 1000000000000) (18919024230 / 1000000000000)))) (orderedInterval (-11762725525 / 1000000000000) (-11762716932 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate464_chunkChecks4_2 :
    compactCertificate464.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1372648740526019 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43001127581 / 1000000000000) (-43001127495 / 1000000000000), orderedInterval (-2398686600 / 1000000000000) (-2398686515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1163609539012459 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21633998810 / 1000000000000) (21634000175 / 1000000000000), orderedInterval (-41514923828 / 1000000000000) (-41514922463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (728132821390777 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33661646048 / 1000000000000) (33661646049 / 1000000000000), orderedInterval (48530282103 / 1000000000000) (48530282104 / 1000000000000)))) (orderedInterval (6941271612 / 1000000000000) (6941271742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (391592253004359 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77544220913 / 1000000000000) (-77544220911 / 1000000000000), orderedInterval (-21733266725 / 1000000000000) (-21733266724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1063249142450077 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20763494462 / 1000000000000) (20763495421 / 1000000000000), orderedInterval (-44354714937 / 1000000000000) (-44354713978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1451775804050429 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26844068475 / 1000000000000) (-26844059123 / 1000000000000), orderedInterval (32184150800 / 1000000000000) (32184160151 / 1000000000000)))) (orderedInterval (2626776893 / 1000000000000) (2626777927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (613867178609223 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-19852500077 / 1000000000000) (-19852500076 / 1000000000000), orderedInterval (-61206468024 / 1000000000000) (-61206468023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2495336000159783 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16907638158 / 1000000000000) (16907638607 / 1000000000000), orderedInterval (-27117562016 / 1000000000000) (-27117561566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1666768804096297 / 4000000000000) 4 (IntervalRat.scale (671 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (13568803727 / 1000000000000) (13568803849 / 1000000000000), orderedInterval (-36672552898 / 1000000000000) (-36672552775 / 1000000000000)))) (orderedInterval (-22352168974 / 1000000000000) (-22352168004 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate464_chunkChecks4 :
    compactCertificate464.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate464.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate464_chunkChecks4_0
    compactCertificate464_chunkChecks4_1 compactCertificate464_chunkChecks4_2

theorem compactCertificate464_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate464.chunkCheck r b = true :=
  compactCertificate464.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate464_chunkChecks0
    · exact compactCertificate464_chunkChecks1
    · exact compactCertificate464_chunkChecks2
    · exact compactCertificate464_chunkChecks3
    · exact compactCertificate464_chunkChecks4)

theorem compactCertificate464_coefficient0 :
    compactCertificate464.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate464_coefficient1 :
    compactCertificate464.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate464_coefficient2 :
    compactCertificate464.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate464_coefficient3 :
    compactCertificate464.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate464_coefficient4 :
    compactCertificate464.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate464_coefficients : ∀ r : Fin 5,
    compactCertificate464.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate464_coefficient0
  · exact compactCertificate464_coefficient1
  · exact compactCertificate464_coefficient2
  · exact compactCertificate464_coefficient3
  · exact compactCertificate464_coefficient4

theorem compactCertificate464_lower : (1 : ℚ) ≤ compactCertificate464.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate464, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate464_proves {t : ℝ} (ht : t ∈ compactCertificate464.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate464.proves compactCertificate464_states compactCertificate464_chunks
    compactCertificate464_coefficients compactCertificate464_lower ht

end Erdos232
