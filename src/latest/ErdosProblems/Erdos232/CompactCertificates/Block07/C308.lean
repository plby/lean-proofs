/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate308 : CompactCertificate where
  left := 181
  right := 182
  center := 363 / 2
  grid := fun i =>
    match i.val with
    | 0 => 58
    | 1 => 43
    | 2 => 69
    | 3 => 12
    | 4 => 33
    | 5 => 91
    | 6 => 67
    | 7 => 114
    | 8 => 84
    | 9 => 129
    | 10 => 75
    | 11 => 132
    | 12 => 124
    | 13 => 88
    | 14 => 100
    | 15 => 83
    | 16 => 74
    | 17 => 107
    | 18 => 59
    | 19 => 50
    | 20 => 31
    | 21 => 17
    | 22 => 46
    | 23 => 63
    | 24 => 26
    | 25 => 107
    | _ => 72
  point := fun i =>
    match i.val with
    | 0 => 363 / 2
    | 1 => 534768314088063 / 4000000000000
    | 2 => 172933085267679 / 800000000000
    | 3 => 156044060319741 / 4000000000000
    | 4 => 419156295431577 / 4000000000000
    | 5 => 1138090879608309 / 4000000000000
    | 6 => 838312590863517 / 4000000000000
    | 7 => 1436462913025041 / 4000000000000
    | 8 => 1058092080231219 / 4000000000000
    | 9 => 1623385351664637 / 4000000000000
    | 10 => 937261969781973 / 4000000000000
    | 11 => 1663187812754457 / 4000000000000
    | 12 => 1553965797723933 / 4000000000000
    | 13 => 1108983318178989 / 4000000000000
    | 14 => 1257468886294731 / 4000000000000
    | 15 => 1048346459670939 / 4000000000000
    | 16 => 926245890277719 / 4000000000000
    | 17 => 268462161170181 / 800000000000
    | 18 => 742580466186207 / 4000000000000
    | 19 => 629493685039527 / 4000000000000
    | 20 => 393907919768781 / 4000000000000
    | 21 => 211844989330227 / 4000000000000
    | 22 => 575200355751681 / 4000000000000
    | 23 => 785386910387937 / 4000000000000
    | 24 => 332092080231219 / 4000000000000
    | 25 => 1349935868938899 / 4000000000000
    | _ => 901694598937341 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (4280297679 / 1000000000000) (4280297680 / 1000000000000), orderedInterval (59057990899 / 1000000000000) (59057990901 / 1000000000000))
    | 1 => (orderedInterval (39640967737 / 1000000000000) (39640980561 / 1000000000000), orderedInterval (-56632244276 / 1000000000000) (-56632231452 / 1000000000000))
    | 2 => (orderedInterval (-9784127427 / 1000000000000) (-9784127426 / 1000000000000), orderedInterval (-53356426737 / 1000000000000) (-53356426736 / 1000000000000))
    | 3 => (orderedInterval (110645466779 / 1000000000000) (110645479997 / 1000000000000), orderedInterval (-65260553531 / 1000000000000) (-65260540313 / 1000000000000))
    | 4 => (orderedInterval (-73739685379 / 1000000000000) (-73739682931 / 1000000000000), orderedInterval (25603648207 / 1000000000000) (25603650655 / 1000000000000))
    | 5 => (orderedInterval (25813933190 / 1000000000000) (25813937329 / 1000000000000), orderedInterval (-39683009113 / 1000000000000) (-39683004973 / 1000000000000))
    | 6 => (orderedInterval (6803489770 / 1000000000000) (6803489789 / 1000000000000), orderedInterval (-54709427192 / 1000000000000) (-54709427172 / 1000000000000))
    | 7 => (orderedInterval (41358752713 / 1000000000000) (41358754822 / 1000000000000), orderedInterval (-7943937152 / 1000000000000) (-7943935043 / 1000000000000))
    | 8 => (orderedInterval (48457221005 / 1000000000000) (48457221015 / 1000000000000), orderedInterval (7561133743 / 1000000000000) (7561133753 / 1000000000000))
    | 9 => (orderedInterval (-38777965638 / 1000000000000) (-38777965623 / 1000000000000), orderedInterval (-8007719340 / 1000000000000) (-8007719325 / 1000000000000))
    | 10 => (orderedInterval (25858368886 / 1000000000000) (25858371789 / 1000000000000), orderedInterval (-45313129378 / 1000000000000) (-45313126475 / 1000000000000))
    | 11 => (orderedInterval (37130044752 / 1000000000000) (37130056265 / 1000000000000), orderedInterval (-12391385246 / 1000000000000) (-12391373733 / 1000000000000))
    | 12 => (orderedInterval (-11224567079 / 1000000000000) (-11224567026 / 1000000000000), orderedInterval (38907983579 / 1000000000000) (38907983631 / 1000000000000))
    | 13 => (orderedInterval (47918938643 / 1000000000000) (47918938762 / 1000000000000), orderedInterval (-78129615 / 1000000000000) (-78129496 / 1000000000000))
    | 14 => (orderedInterval (37694760185 / 1000000000000) (37694760186 / 1000000000000), orderedInterval (24520266459 / 1000000000000) (24520266460 / 1000000000000))
    | 15 => (orderedInterval (-42054254016 / 1000000000000) (-42054207364 / 1000000000000), orderedInterval (25780069712 / 1000000000000) (25780116363 / 1000000000000))
    | 16 => (orderedInterval (-6876434480 / 1000000000000) (-6876434461 / 1000000000000), orderedInterval (51995307871 / 1000000000000) (51995307889 / 1000000000000))
    | 17 => (orderedInterval (-9178095696 / 1000000000000) (-9178095695 / 1000000000000), orderedInterval (-42563907291 / 1000000000000) (-42563907290 / 1000000000000))
    | 18 => (orderedInterval (-51532729009 / 1000000000000) (-51532729008 / 1000000000000), orderedInterval (-27674888339 / 1000000000000) (-27674888338 / 1000000000000))
    | 19 => (orderedInterval (56046341018 / 1000000000000) (56046341019 / 1000000000000), orderedInterval (29889819629 / 1000000000000) (29889819630 / 1000000000000))
    | 20 => (orderedInterval (-76789129790 / 1000000000000) (-76789128085 / 1000000000000), orderedInterval (24222974158 / 1000000000000) (24222975864 / 1000000000000))
    | 21 => (orderedInterval (-36273579404 / 1000000000000) (-36273579403 / 1000000000000), orderedInterval (-103123167912 / 1000000000000) (-103123167911 / 1000000000000))
    | 22 => (orderedInterval (4743728411 / 1000000000000) (4743728413 / 1000000000000), orderedInterval (66350969500 / 1000000000000) (66350969502 / 1000000000000))
    | 23 => (orderedInterval (40402231366 / 1000000000000) (40402280847 / 1000000000000), orderedInterval (-40227487602 / 1000000000000) (-40227438121 / 1000000000000))
    | 24 => (orderedInterval (74436099417 / 1000000000000) (74436121171 / 1000000000000), orderedInterval (-46569798997 / 1000000000000) (-46569777243 / 1000000000000))
    | 25 => (orderedInterval (-37077366729 / 1000000000000) (-37077302036 / 1000000000000), orderedInterval (22674374025 / 1000000000000) (22674438718 / 1000000000000))
    | _ => (orderedInterval (734526258 / 1000000000000) (734526260 / 1000000000000), orderedInterval (53135656719 / 1000000000000) (53135656722 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1491793317 / 1000000000000) (1491793451 / 1000000000000)
      | 1 => orderedInterval (-5727893222 / 1000000000000) (-5727892672 / 1000000000000)
      | 2 => orderedInterval (-104554055 / 1000000000000) (-104553979 / 1000000000000)
      | 3 => orderedInterval (14084523227 / 1000000000000) (14084525154 / 1000000000000)
      | 4 => orderedInterval (4543233038 / 1000000000000) (4543233072 / 1000000000000)
      | 5 => orderedInterval (-327108666 / 1000000000000) (-327108108 / 1000000000000)
      | 6 => orderedInterval (2567582495 / 1000000000000) (2567582597 / 1000000000000)
      | 7 => orderedInterval (-2534209585 / 1000000000000) (-2534205770 / 1000000000000)
      | _ => orderedInterval (3329066858 / 1000000000000) (3329072306 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19290779239 / 1000000000000) (19290779343 / 1000000000000)
      | 1 => orderedInterval (5114238852 / 1000000000000) (5114239421 / 1000000000000)
      | 2 => orderedInterval (751128608 / 1000000000000) (751128756 / 1000000000000)
      | 3 => orderedInterval (-5188075253 / 1000000000000) (-5188071070 / 1000000000000)
      | 4 => orderedInterval (-1729680884 / 1000000000000) (-1729680829 / 1000000000000)
      | 5 => orderedInterval (-5381302195 / 1000000000000) (-5381301390 / 1000000000000)
      | 6 => orderedInterval (3487050812 / 1000000000000) (3487050885 / 1000000000000)
      | 7 => orderedInterval (2698183562 / 1000000000000) (2698187684 / 1000000000000)
      | _ => orderedInterval (-15942766428 / 1000000000000) (-15942756504 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1188848499 / 1000000000000) (-1188848416 / 1000000000000)
      | 1 => orderedInterval (5434366650 / 1000000000000) (5434367447 / 1000000000000)
      | 2 => orderedInterval (2502362316 / 1000000000000) (2502362604 / 1000000000000)
      | 3 => orderedInterval (-65317730285 / 1000000000000) (-65317720982 / 1000000000000)
      | 4 => orderedInterval (-10919744181 / 1000000000000) (-10919744091 / 1000000000000)
      | 5 => orderedInterval (1205049128 / 1000000000000) (1205050296 / 1000000000000)
      | 6 => orderedInterval (-5518715936 / 1000000000000) (-5518715879 / 1000000000000)
      | 7 => orderedInterval (3619327922 / 1000000000000) (3619332403 / 1000000000000)
      | _ => orderedInterval (-10228540533 / 1000000000000) (-10228522139 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17900922715 / 1000000000000) (-17900922647 / 1000000000000)
      | 1 => orderedInterval (-11084281495 / 1000000000000) (-11084280286 / 1000000000000)
      | 2 => orderedInterval (-2477396291 / 1000000000000) (-2477395727 / 1000000000000)
      | 3 => orderedInterval (12853969644 / 1000000000000) (12853990564 / 1000000000000)
      | 4 => orderedInterval (7619400676 / 1000000000000) (7619400825 / 1000000000000)
      | 5 => orderedInterval (12164101317 / 1000000000000) (12164103006 / 1000000000000)
      | 6 => orderedInterval (-3727786135 / 1000000000000) (-3727786086 / 1000000000000)
      | 7 => orderedInterval (-3221666704 / 1000000000000) (-3221661858 / 1000000000000)
      | _ => orderedInterval (31049268587 / 1000000000000) (31049302716 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (847290443 / 1000000000000) (847290502 / 1000000000000)
      | 1 => orderedInterval (-11261503538 / 1000000000000) (-11261501658 / 1000000000000)
      | 2 => orderedInterval (-14239833468 / 1000000000000) (-14239832357 / 1000000000000)
      | 3 => orderedInterval (322819167414 / 1000000000000) (322819214934 / 1000000000000)
      | 4 => orderedInterval (27123029531 / 1000000000000) (27123029785 / 1000000000000)
      | 5 => orderedInterval (-3948985084 / 1000000000000) (-3948982629 / 1000000000000)
      | 6 => orderedInterval (7049844079 / 1000000000000) (7049844124 / 1000000000000)
      | 7 => orderedInterval (-4242694478 / 1000000000000) (-4242689210 / 1000000000000)
      | _ => orderedInterval (35427724782 / 1000000000000) (35427788370 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17322433407 / 1000000000000) (17322446051 / 1000000000000)
    | 1 => orderedInterval (3099556313 / 1000000000000) (3099576296 / 1000000000000)
    | 2 => orderedInterval (-80412473418 / 1000000000000) (-80412438757 / 1000000000000)
    | 3 => orderedInterval (25274686884 / 1000000000000) (25274750507 / 1000000000000)
    | _ => orderedInterval (359574039681 / 1000000000000) (359574161861 / 1000000000000)

theorem compactCertificate308_stateChecks0 :
    compactCertificate308.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (363 / 2)) (orderedInterval (4280297679 / 1000000000000) (4280297680 / 1000000000000), orderedInterval (59057990899 / 1000000000000) (59057990901 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (534768314088063 / 4000000000000)) (orderedInterval (39640967737 / 1000000000000) (39640980561 / 1000000000000), orderedInterval (-56632244276 / 1000000000000) (-56632231452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (172933085267679 / 800000000000)) (orderedInterval (-9784127427 / 1000000000000) (-9784127426 / 1000000000000), orderedInterval (-53356426737 / 1000000000000) (-53356426736 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks1 :
    compactCertificate308.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (156044060319741 / 4000000000000)) (orderedInterval (110645466779 / 1000000000000) (110645479997 / 1000000000000), orderedInterval (-65260553531 / 1000000000000) (-65260540313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (419156295431577 / 4000000000000)) (orderedInterval (-73739685379 / 1000000000000) (-73739682931 / 1000000000000), orderedInterval (25603648207 / 1000000000000) (25603650655 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1138090879608309 / 4000000000000)) (orderedInterval (25813933190 / 1000000000000) (25813937329 / 1000000000000), orderedInterval (-39683009113 / 1000000000000) (-39683004973 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks2 :
    compactCertificate308.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (838312590863517 / 4000000000000)) (orderedInterval (6803489770 / 1000000000000) (6803489789 / 1000000000000), orderedInterval (-54709427192 / 1000000000000) (-54709427172 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1436462913025041 / 4000000000000)) (orderedInterval (41358752713 / 1000000000000) (41358754822 / 1000000000000), orderedInterval (-7943937152 / 1000000000000) (-7943935043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1058092080231219 / 4000000000000)) (orderedInterval (48457221005 / 1000000000000) (48457221015 / 1000000000000), orderedInterval (7561133743 / 1000000000000) (7561133753 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks3 :
    compactCertificate308.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1623385351664637 / 4000000000000)) (orderedInterval (-38777965638 / 1000000000000) (-38777965623 / 1000000000000), orderedInterval (-8007719340 / 1000000000000) (-8007719325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (937261969781973 / 4000000000000)) (orderedInterval (25858368886 / 1000000000000) (25858371789 / 1000000000000), orderedInterval (-45313129378 / 1000000000000) (-45313126475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1663187812754457 / 4000000000000)) (orderedInterval (37130044752 / 1000000000000) (37130056265 / 1000000000000), orderedInterval (-12391385246 / 1000000000000) (-12391373733 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks4 :
    compactCertificate308.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1553965797723933 / 4000000000000)) (orderedInterval (-11224567079 / 1000000000000) (-11224567026 / 1000000000000), orderedInterval (38907983579 / 1000000000000) (38907983631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1108983318178989 / 4000000000000)) (orderedInterval (47918938643 / 1000000000000) (47918938762 / 1000000000000), orderedInterval (-78129615 / 1000000000000) (-78129496 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1257468886294731 / 4000000000000)) (orderedInterval (37694760185 / 1000000000000) (37694760186 / 1000000000000), orderedInterval (24520266459 / 1000000000000) (24520266460 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks5 :
    compactCertificate308.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1048346459670939 / 4000000000000)) (orderedInterval (-42054254016 / 1000000000000) (-42054207364 / 1000000000000), orderedInterval (25780069712 / 1000000000000) (25780116363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (926245890277719 / 4000000000000)) (orderedInterval (-6876434480 / 1000000000000) (-6876434461 / 1000000000000), orderedInterval (51995307871 / 1000000000000) (51995307889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (268462161170181 / 800000000000)) (orderedInterval (-9178095696 / 1000000000000) (-9178095695 / 1000000000000), orderedInterval (-42563907291 / 1000000000000) (-42563907290 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks6 :
    compactCertificate308.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (742580466186207 / 4000000000000)) (orderedInterval (-51532729009 / 1000000000000) (-51532729008 / 1000000000000), orderedInterval (-27674888339 / 1000000000000) (-27674888338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (629493685039527 / 4000000000000)) (orderedInterval (56046341018 / 1000000000000) (56046341019 / 1000000000000), orderedInterval (29889819629 / 1000000000000) (29889819630 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (393907919768781 / 4000000000000)) (orderedInterval (-76789129790 / 1000000000000) (-76789128085 / 1000000000000), orderedInterval (24222974158 / 1000000000000) (24222975864 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks7 :
    compactCertificate308.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (211844989330227 / 4000000000000)) (orderedInterval (-36273579404 / 1000000000000) (-36273579403 / 1000000000000), orderedInterval (-103123167912 / 1000000000000) (-103123167911 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (575200355751681 / 4000000000000)) (orderedInterval (4743728411 / 1000000000000) (4743728413 / 1000000000000), orderedInterval (66350969500 / 1000000000000) (66350969502 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (785386910387937 / 4000000000000)) (orderedInterval (40402231366 / 1000000000000) (40402280847 / 1000000000000), orderedInterval (-40227487602 / 1000000000000) (-40227438121 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_stateChecks8 :
    compactCertificate308.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (332092080231219 / 4000000000000)) (orderedInterval (74436099417 / 1000000000000) (74436121171 / 1000000000000), orderedInterval (-46569798997 / 1000000000000) (-46569777243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1349935868938899 / 4000000000000)) (orderedInterval (-37077366729 / 1000000000000) (-37077302036 / 1000000000000), orderedInterval (22674374025 / 1000000000000) (22674438718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (901694598937341 / 4000000000000)) (orderedInterval (734526258 / 1000000000000) (734526260 / 1000000000000), orderedInterval (53135656719 / 1000000000000) (53135656722 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_states : ∀ j,
    BesselStateValid (compactCertificate308.point j) (compactCertificate308.state j) :=
  compactCertificate308.statesValid_of_checks3 compactCertificate308_stateChecks0
    compactCertificate308_stateChecks1 compactCertificate308_stateChecks2
    compactCertificate308_stateChecks3 compactCertificate308_stateChecks4
    compactCertificate308_stateChecks5 compactCertificate308_stateChecks6
    compactCertificate308_stateChecks7 compactCertificate308_stateChecks8

theorem compactCertificate308_chunkChecks0_0 :
    compactCertificate308.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (363 / 2) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4280297679 / 1000000000000) (4280297680 / 1000000000000), orderedInterval (59057990899 / 1000000000000) (59057990901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (534768314088063 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39640967737 / 1000000000000) (39640980561 / 1000000000000), orderedInterval (-56632244276 / 1000000000000) (-56632231452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (172933085267679 / 800000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9784127427 / 1000000000000) (-9784127426 / 1000000000000), orderedInterval (-53356426737 / 1000000000000) (-53356426736 / 1000000000000)))) (orderedInterval (1491793317 / 1000000000000) (1491793451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (156044060319741 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110645466779 / 1000000000000) (110645479997 / 1000000000000), orderedInterval (-65260553531 / 1000000000000) (-65260540313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (419156295431577 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73739685379 / 1000000000000) (-73739682931 / 1000000000000), orderedInterval (25603648207 / 1000000000000) (25603650655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1138090879608309 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25813933190 / 1000000000000) (25813937329 / 1000000000000), orderedInterval (-39683009113 / 1000000000000) (-39683004973 / 1000000000000)))) (orderedInterval (-5727893222 / 1000000000000) (-5727892672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (838312590863517 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6803489770 / 1000000000000) (6803489789 / 1000000000000), orderedInterval (-54709427192 / 1000000000000) (-54709427172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1436462913025041 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41358752713 / 1000000000000) (41358754822 / 1000000000000), orderedInterval (-7943937152 / 1000000000000) (-7943935043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1058092080231219 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48457221005 / 1000000000000) (48457221015 / 1000000000000), orderedInterval (7561133743 / 1000000000000) (7561133753 / 1000000000000)))) (orderedInterval (-104554055 / 1000000000000) (-104553979 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks0_1 :
    compactCertificate308.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1623385351664637 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38777965638 / 1000000000000) (-38777965623 / 1000000000000), orderedInterval (-8007719340 / 1000000000000) (-8007719325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (937261969781973 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25858368886 / 1000000000000) (25858371789 / 1000000000000), orderedInterval (-45313129378 / 1000000000000) (-45313126475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1663187812754457 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37130044752 / 1000000000000) (37130056265 / 1000000000000), orderedInterval (-12391385246 / 1000000000000) (-12391373733 / 1000000000000)))) (orderedInterval (14084523227 / 1000000000000) (14084525154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1553965797723933 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11224567079 / 1000000000000) (-11224567026 / 1000000000000), orderedInterval (38907983579 / 1000000000000) (38907983631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1108983318178989 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47918938643 / 1000000000000) (47918938762 / 1000000000000), orderedInterval (-78129615 / 1000000000000) (-78129496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1257468886294731 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37694760185 / 1000000000000) (37694760186 / 1000000000000), orderedInterval (24520266459 / 1000000000000) (24520266460 / 1000000000000)))) (orderedInterval (4543233038 / 1000000000000) (4543233072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1048346459670939 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42054254016 / 1000000000000) (-42054207364 / 1000000000000), orderedInterval (25780069712 / 1000000000000) (25780116363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (926245890277719 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6876434480 / 1000000000000) (-6876434461 / 1000000000000), orderedInterval (51995307871 / 1000000000000) (51995307889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (268462161170181 / 800000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9178095696 / 1000000000000) (-9178095695 / 1000000000000), orderedInterval (-42563907291 / 1000000000000) (-42563907290 / 1000000000000)))) (orderedInterval (-327108666 / 1000000000000) (-327108108 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks0_2 :
    compactCertificate308.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (742580466186207 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-51532729009 / 1000000000000) (-51532729008 / 1000000000000), orderedInterval (-27674888339 / 1000000000000) (-27674888338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (629493685039527 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56046341018 / 1000000000000) (56046341019 / 1000000000000), orderedInterval (29889819629 / 1000000000000) (29889819630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (393907919768781 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76789129790 / 1000000000000) (-76789128085 / 1000000000000), orderedInterval (24222974158 / 1000000000000) (24222975864 / 1000000000000)))) (orderedInterval (2567582495 / 1000000000000) (2567582597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (211844989330227 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36273579404 / 1000000000000) (-36273579403 / 1000000000000), orderedInterval (-103123167912 / 1000000000000) (-103123167911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (575200355751681 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4743728411 / 1000000000000) (4743728413 / 1000000000000), orderedInterval (66350969500 / 1000000000000) (66350969502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (785386910387937 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40402231366 / 1000000000000) (40402280847 / 1000000000000), orderedInterval (-40227487602 / 1000000000000) (-40227438121 / 1000000000000)))) (orderedInterval (-2534209585 / 1000000000000) (-2534205770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (332092080231219 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (74436099417 / 1000000000000) (74436121171 / 1000000000000), orderedInterval (-46569798997 / 1000000000000) (-46569777243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1349935868938899 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37077366729 / 1000000000000) (-37077302036 / 1000000000000), orderedInterval (22674374025 / 1000000000000) (22674438718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (901694598937341 / 4000000000000) 0 (IntervalRat.scale (363 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (734526258 / 1000000000000) (734526260 / 1000000000000), orderedInterval (53135656719 / 1000000000000) (53135656722 / 1000000000000)))) (orderedInterval (3329066858 / 1000000000000) (3329072306 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks0 :
    compactCertificate308.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate308.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate308_chunkChecks0_0
    compactCertificate308_chunkChecks0_1 compactCertificate308_chunkChecks0_2

theorem compactCertificate308_chunkChecks1_0 :
    compactCertificate308.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (363 / 2) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4280297679 / 1000000000000) (4280297680 / 1000000000000), orderedInterval (59057990899 / 1000000000000) (59057990901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (534768314088063 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39640967737 / 1000000000000) (39640980561 / 1000000000000), orderedInterval (-56632244276 / 1000000000000) (-56632231452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (172933085267679 / 800000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9784127427 / 1000000000000) (-9784127426 / 1000000000000), orderedInterval (-53356426737 / 1000000000000) (-53356426736 / 1000000000000)))) (orderedInterval (19290779239 / 1000000000000) (19290779343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (156044060319741 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110645466779 / 1000000000000) (110645479997 / 1000000000000), orderedInterval (-65260553531 / 1000000000000) (-65260540313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (419156295431577 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73739685379 / 1000000000000) (-73739682931 / 1000000000000), orderedInterval (25603648207 / 1000000000000) (25603650655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1138090879608309 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25813933190 / 1000000000000) (25813937329 / 1000000000000), orderedInterval (-39683009113 / 1000000000000) (-39683004973 / 1000000000000)))) (orderedInterval (5114238852 / 1000000000000) (5114239421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (838312590863517 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6803489770 / 1000000000000) (6803489789 / 1000000000000), orderedInterval (-54709427192 / 1000000000000) (-54709427172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1436462913025041 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41358752713 / 1000000000000) (41358754822 / 1000000000000), orderedInterval (-7943937152 / 1000000000000) (-7943935043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1058092080231219 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48457221005 / 1000000000000) (48457221015 / 1000000000000), orderedInterval (7561133743 / 1000000000000) (7561133753 / 1000000000000)))) (orderedInterval (751128608 / 1000000000000) (751128756 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks1_1 :
    compactCertificate308.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1623385351664637 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38777965638 / 1000000000000) (-38777965623 / 1000000000000), orderedInterval (-8007719340 / 1000000000000) (-8007719325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (937261969781973 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25858368886 / 1000000000000) (25858371789 / 1000000000000), orderedInterval (-45313129378 / 1000000000000) (-45313126475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1663187812754457 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37130044752 / 1000000000000) (37130056265 / 1000000000000), orderedInterval (-12391385246 / 1000000000000) (-12391373733 / 1000000000000)))) (orderedInterval (-5188075253 / 1000000000000) (-5188071070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1553965797723933 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11224567079 / 1000000000000) (-11224567026 / 1000000000000), orderedInterval (38907983579 / 1000000000000) (38907983631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1108983318178989 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47918938643 / 1000000000000) (47918938762 / 1000000000000), orderedInterval (-78129615 / 1000000000000) (-78129496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1257468886294731 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37694760185 / 1000000000000) (37694760186 / 1000000000000), orderedInterval (24520266459 / 1000000000000) (24520266460 / 1000000000000)))) (orderedInterval (-1729680884 / 1000000000000) (-1729680829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1048346459670939 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42054254016 / 1000000000000) (-42054207364 / 1000000000000), orderedInterval (25780069712 / 1000000000000) (25780116363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (926245890277719 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6876434480 / 1000000000000) (-6876434461 / 1000000000000), orderedInterval (51995307871 / 1000000000000) (51995307889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (268462161170181 / 800000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9178095696 / 1000000000000) (-9178095695 / 1000000000000), orderedInterval (-42563907291 / 1000000000000) (-42563907290 / 1000000000000)))) (orderedInterval (-5381302195 / 1000000000000) (-5381301390 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks1_2 :
    compactCertificate308.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (742580466186207 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-51532729009 / 1000000000000) (-51532729008 / 1000000000000), orderedInterval (-27674888339 / 1000000000000) (-27674888338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (629493685039527 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56046341018 / 1000000000000) (56046341019 / 1000000000000), orderedInterval (29889819629 / 1000000000000) (29889819630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (393907919768781 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76789129790 / 1000000000000) (-76789128085 / 1000000000000), orderedInterval (24222974158 / 1000000000000) (24222975864 / 1000000000000)))) (orderedInterval (3487050812 / 1000000000000) (3487050885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (211844989330227 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36273579404 / 1000000000000) (-36273579403 / 1000000000000), orderedInterval (-103123167912 / 1000000000000) (-103123167911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (575200355751681 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4743728411 / 1000000000000) (4743728413 / 1000000000000), orderedInterval (66350969500 / 1000000000000) (66350969502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (785386910387937 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40402231366 / 1000000000000) (40402280847 / 1000000000000), orderedInterval (-40227487602 / 1000000000000) (-40227438121 / 1000000000000)))) (orderedInterval (2698183562 / 1000000000000) (2698187684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (332092080231219 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (74436099417 / 1000000000000) (74436121171 / 1000000000000), orderedInterval (-46569798997 / 1000000000000) (-46569777243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1349935868938899 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37077366729 / 1000000000000) (-37077302036 / 1000000000000), orderedInterval (22674374025 / 1000000000000) (22674438718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (901694598937341 / 4000000000000) 1 (IntervalRat.scale (363 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (734526258 / 1000000000000) (734526260 / 1000000000000), orderedInterval (53135656719 / 1000000000000) (53135656722 / 1000000000000)))) (orderedInterval (-15942766428 / 1000000000000) (-15942756504 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks1 :
    compactCertificate308.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate308.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate308_chunkChecks1_0
    compactCertificate308_chunkChecks1_1 compactCertificate308_chunkChecks1_2

theorem compactCertificate308_chunkChecks2_0 :
    compactCertificate308.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (363 / 2) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4280297679 / 1000000000000) (4280297680 / 1000000000000), orderedInterval (59057990899 / 1000000000000) (59057990901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (534768314088063 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39640967737 / 1000000000000) (39640980561 / 1000000000000), orderedInterval (-56632244276 / 1000000000000) (-56632231452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (172933085267679 / 800000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9784127427 / 1000000000000) (-9784127426 / 1000000000000), orderedInterval (-53356426737 / 1000000000000) (-53356426736 / 1000000000000)))) (orderedInterval (-1188848499 / 1000000000000) (-1188848416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (156044060319741 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110645466779 / 1000000000000) (110645479997 / 1000000000000), orderedInterval (-65260553531 / 1000000000000) (-65260540313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (419156295431577 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73739685379 / 1000000000000) (-73739682931 / 1000000000000), orderedInterval (25603648207 / 1000000000000) (25603650655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1138090879608309 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25813933190 / 1000000000000) (25813937329 / 1000000000000), orderedInterval (-39683009113 / 1000000000000) (-39683004973 / 1000000000000)))) (orderedInterval (5434366650 / 1000000000000) (5434367447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (838312590863517 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6803489770 / 1000000000000) (6803489789 / 1000000000000), orderedInterval (-54709427192 / 1000000000000) (-54709427172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1436462913025041 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41358752713 / 1000000000000) (41358754822 / 1000000000000), orderedInterval (-7943937152 / 1000000000000) (-7943935043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1058092080231219 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48457221005 / 1000000000000) (48457221015 / 1000000000000), orderedInterval (7561133743 / 1000000000000) (7561133753 / 1000000000000)))) (orderedInterval (2502362316 / 1000000000000) (2502362604 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks2_1 :
    compactCertificate308.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1623385351664637 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38777965638 / 1000000000000) (-38777965623 / 1000000000000), orderedInterval (-8007719340 / 1000000000000) (-8007719325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (937261969781973 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25858368886 / 1000000000000) (25858371789 / 1000000000000), orderedInterval (-45313129378 / 1000000000000) (-45313126475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1663187812754457 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37130044752 / 1000000000000) (37130056265 / 1000000000000), orderedInterval (-12391385246 / 1000000000000) (-12391373733 / 1000000000000)))) (orderedInterval (-65317730285 / 1000000000000) (-65317720982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1553965797723933 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11224567079 / 1000000000000) (-11224567026 / 1000000000000), orderedInterval (38907983579 / 1000000000000) (38907983631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1108983318178989 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47918938643 / 1000000000000) (47918938762 / 1000000000000), orderedInterval (-78129615 / 1000000000000) (-78129496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1257468886294731 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37694760185 / 1000000000000) (37694760186 / 1000000000000), orderedInterval (24520266459 / 1000000000000) (24520266460 / 1000000000000)))) (orderedInterval (-10919744181 / 1000000000000) (-10919744091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1048346459670939 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42054254016 / 1000000000000) (-42054207364 / 1000000000000), orderedInterval (25780069712 / 1000000000000) (25780116363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (926245890277719 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6876434480 / 1000000000000) (-6876434461 / 1000000000000), orderedInterval (51995307871 / 1000000000000) (51995307889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (268462161170181 / 800000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9178095696 / 1000000000000) (-9178095695 / 1000000000000), orderedInterval (-42563907291 / 1000000000000) (-42563907290 / 1000000000000)))) (orderedInterval (1205049128 / 1000000000000) (1205050296 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks2_2 :
    compactCertificate308.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (742580466186207 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-51532729009 / 1000000000000) (-51532729008 / 1000000000000), orderedInterval (-27674888339 / 1000000000000) (-27674888338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (629493685039527 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56046341018 / 1000000000000) (56046341019 / 1000000000000), orderedInterval (29889819629 / 1000000000000) (29889819630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (393907919768781 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76789129790 / 1000000000000) (-76789128085 / 1000000000000), orderedInterval (24222974158 / 1000000000000) (24222975864 / 1000000000000)))) (orderedInterval (-5518715936 / 1000000000000) (-5518715879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (211844989330227 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36273579404 / 1000000000000) (-36273579403 / 1000000000000), orderedInterval (-103123167912 / 1000000000000) (-103123167911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (575200355751681 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4743728411 / 1000000000000) (4743728413 / 1000000000000), orderedInterval (66350969500 / 1000000000000) (66350969502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (785386910387937 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40402231366 / 1000000000000) (40402280847 / 1000000000000), orderedInterval (-40227487602 / 1000000000000) (-40227438121 / 1000000000000)))) (orderedInterval (3619327922 / 1000000000000) (3619332403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (332092080231219 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (74436099417 / 1000000000000) (74436121171 / 1000000000000), orderedInterval (-46569798997 / 1000000000000) (-46569777243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1349935868938899 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37077366729 / 1000000000000) (-37077302036 / 1000000000000), orderedInterval (22674374025 / 1000000000000) (22674438718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (901694598937341 / 4000000000000) 2 (IntervalRat.scale (363 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (734526258 / 1000000000000) (734526260 / 1000000000000), orderedInterval (53135656719 / 1000000000000) (53135656722 / 1000000000000)))) (orderedInterval (-10228540533 / 1000000000000) (-10228522139 / 1000000000000))) = true
  rfl'

theorem compactCertificate308_chunkChecks2 :
    compactCertificate308.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate308.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate308_chunkChecks2_0
    compactCertificate308_chunkChecks2_1 compactCertificate308_chunkChecks2_2

theorem compactCertificate308_chunkChecks3_0 :
    compactCertificate308.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (363 / 2) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4280297679 / 1000000000000) (4280297680 / 1000000000000), orderedInterval (59057990899 / 1000000000000) (59057990901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (534768314088063 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39640967737 / 1000000000000) (39640980561 / 1000000000000), orderedInterval (-56632244276 / 1000000000000) (-56632231452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (172933085267679 / 800000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9784127427 / 1000000000000) (-9784127426 / 1000000000000), orderedInterval (-53356426737 / 1000000000000) (-53356426736 / 1000000000000)))) (orderedInterval (-17900922715 / 1000000000000) (-17900922647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (156044060319741 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110645466779 / 1000000000000) (110645479997 / 1000000000000), orderedInterval (-65260553531 / 1000000000000) (-65260540313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (419156295431577 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73739685379 / 1000000000000) (-73739682931 / 1000000000000), orderedInterval (25603648207 / 1000000000000) (25603650655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1138090879608309 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25813933190 / 1000000000000) (25813937329 / 1000000000000), orderedInterval (-39683009113 / 1000000000000) (-39683004973 / 1000000000000)))) (orderedInterval (-11084281495 / 1000000000000) (-11084280286 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (838312590863517 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6803489770 / 1000000000000) (6803489789 / 1000000000000), orderedInterval (-54709427192 / 1000000000000) (-54709427172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1436462913025041 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41358752713 / 1000000000000) (41358754822 / 1000000000000), orderedInterval (-7943937152 / 1000000000000) (-7943935043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1058092080231219 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48457221005 / 1000000000000) (48457221015 / 1000000000000), orderedInterval (7561133743 / 1000000000000) (7561133753 / 1000000000000)))) (orderedInterval (-2477396291 / 1000000000000) (-2477395727 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate308_chunkChecks3_1 :
    compactCertificate308.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1623385351664637 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38777965638 / 1000000000000) (-38777965623 / 1000000000000), orderedInterval (-8007719340 / 1000000000000) (-8007719325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (937261969781973 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25858368886 / 1000000000000) (25858371789 / 1000000000000), orderedInterval (-45313129378 / 1000000000000) (-45313126475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1663187812754457 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37130044752 / 1000000000000) (37130056265 / 1000000000000), orderedInterval (-12391385246 / 1000000000000) (-12391373733 / 1000000000000)))) (orderedInterval (12853969644 / 1000000000000) (12853990564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1553965797723933 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11224567079 / 1000000000000) (-11224567026 / 1000000000000), orderedInterval (38907983579 / 1000000000000) (38907983631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1108983318178989 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47918938643 / 1000000000000) (47918938762 / 1000000000000), orderedInterval (-78129615 / 1000000000000) (-78129496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1257468886294731 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37694760185 / 1000000000000) (37694760186 / 1000000000000), orderedInterval (24520266459 / 1000000000000) (24520266460 / 1000000000000)))) (orderedInterval (7619400676 / 1000000000000) (7619400825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1048346459670939 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42054254016 / 1000000000000) (-42054207364 / 1000000000000), orderedInterval (25780069712 / 1000000000000) (25780116363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (926245890277719 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6876434480 / 1000000000000) (-6876434461 / 1000000000000), orderedInterval (51995307871 / 1000000000000) (51995307889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (268462161170181 / 800000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9178095696 / 1000000000000) (-9178095695 / 1000000000000), orderedInterval (-42563907291 / 1000000000000) (-42563907290 / 1000000000000)))) (orderedInterval (12164101317 / 1000000000000) (12164103006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate308_chunkChecks3_2 :
    compactCertificate308.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (742580466186207 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-51532729009 / 1000000000000) (-51532729008 / 1000000000000), orderedInterval (-27674888339 / 1000000000000) (-27674888338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (629493685039527 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56046341018 / 1000000000000) (56046341019 / 1000000000000), orderedInterval (29889819629 / 1000000000000) (29889819630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (393907919768781 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76789129790 / 1000000000000) (-76789128085 / 1000000000000), orderedInterval (24222974158 / 1000000000000) (24222975864 / 1000000000000)))) (orderedInterval (-3727786135 / 1000000000000) (-3727786086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (211844989330227 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36273579404 / 1000000000000) (-36273579403 / 1000000000000), orderedInterval (-103123167912 / 1000000000000) (-103123167911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (575200355751681 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4743728411 / 1000000000000) (4743728413 / 1000000000000), orderedInterval (66350969500 / 1000000000000) (66350969502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (785386910387937 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40402231366 / 1000000000000) (40402280847 / 1000000000000), orderedInterval (-40227487602 / 1000000000000) (-40227438121 / 1000000000000)))) (orderedInterval (-3221666704 / 1000000000000) (-3221661858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (332092080231219 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (74436099417 / 1000000000000) (74436121171 / 1000000000000), orderedInterval (-46569798997 / 1000000000000) (-46569777243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1349935868938899 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37077366729 / 1000000000000) (-37077302036 / 1000000000000), orderedInterval (22674374025 / 1000000000000) (22674438718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (901694598937341 / 4000000000000) 3 (IntervalRat.scale (363 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (734526258 / 1000000000000) (734526260 / 1000000000000), orderedInterval (53135656719 / 1000000000000) (53135656722 / 1000000000000)))) (orderedInterval (31049268587 / 1000000000000) (31049302716 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate308_chunkChecks3 :
    compactCertificate308.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate308.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate308_chunkChecks3_0
    compactCertificate308_chunkChecks3_1 compactCertificate308_chunkChecks3_2

theorem compactCertificate308_chunkChecks4_0 :
    compactCertificate308.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (363 / 2) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4280297679 / 1000000000000) (4280297680 / 1000000000000), orderedInterval (59057990899 / 1000000000000) (59057990901 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (534768314088063 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (39640967737 / 1000000000000) (39640980561 / 1000000000000), orderedInterval (-56632244276 / 1000000000000) (-56632231452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (172933085267679 / 800000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9784127427 / 1000000000000) (-9784127426 / 1000000000000), orderedInterval (-53356426737 / 1000000000000) (-53356426736 / 1000000000000)))) (orderedInterval (847290443 / 1000000000000) (847290502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (156044060319741 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110645466779 / 1000000000000) (110645479997 / 1000000000000), orderedInterval (-65260553531 / 1000000000000) (-65260540313 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (419156295431577 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-73739685379 / 1000000000000) (-73739682931 / 1000000000000), orderedInterval (25603648207 / 1000000000000) (25603650655 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1138090879608309 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25813933190 / 1000000000000) (25813937329 / 1000000000000), orderedInterval (-39683009113 / 1000000000000) (-39683004973 / 1000000000000)))) (orderedInterval (-11261503538 / 1000000000000) (-11261501658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (838312590863517 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (6803489770 / 1000000000000) (6803489789 / 1000000000000), orderedInterval (-54709427192 / 1000000000000) (-54709427172 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1436462913025041 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (41358752713 / 1000000000000) (41358754822 / 1000000000000), orderedInterval (-7943937152 / 1000000000000) (-7943935043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1058092080231219 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (48457221005 / 1000000000000) (48457221015 / 1000000000000), orderedInterval (7561133743 / 1000000000000) (7561133753 / 1000000000000)))) (orderedInterval (-14239833468 / 1000000000000) (-14239832357 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate308_chunkChecks4_1 :
    compactCertificate308.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1623385351664637 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-38777965638 / 1000000000000) (-38777965623 / 1000000000000), orderedInterval (-8007719340 / 1000000000000) (-8007719325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (937261969781973 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25858368886 / 1000000000000) (25858371789 / 1000000000000), orderedInterval (-45313129378 / 1000000000000) (-45313126475 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1663187812754457 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (37130044752 / 1000000000000) (37130056265 / 1000000000000), orderedInterval (-12391385246 / 1000000000000) (-12391373733 / 1000000000000)))) (orderedInterval (322819167414 / 1000000000000) (322819214934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1553965797723933 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11224567079 / 1000000000000) (-11224567026 / 1000000000000), orderedInterval (38907983579 / 1000000000000) (38907983631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1108983318178989 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47918938643 / 1000000000000) (47918938762 / 1000000000000), orderedInterval (-78129615 / 1000000000000) (-78129496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1257468886294731 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37694760185 / 1000000000000) (37694760186 / 1000000000000), orderedInterval (24520266459 / 1000000000000) (24520266460 / 1000000000000)))) (orderedInterval (27123029531 / 1000000000000) (27123029785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1048346459670939 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42054254016 / 1000000000000) (-42054207364 / 1000000000000), orderedInterval (25780069712 / 1000000000000) (25780116363 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (926245890277719 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6876434480 / 1000000000000) (-6876434461 / 1000000000000), orderedInterval (51995307871 / 1000000000000) (51995307889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (268462161170181 / 800000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9178095696 / 1000000000000) (-9178095695 / 1000000000000), orderedInterval (-42563907291 / 1000000000000) (-42563907290 / 1000000000000)))) (orderedInterval (-3948985084 / 1000000000000) (-3948982629 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate308_chunkChecks4_2 :
    compactCertificate308.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (742580466186207 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-51532729009 / 1000000000000) (-51532729008 / 1000000000000), orderedInterval (-27674888339 / 1000000000000) (-27674888338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (629493685039527 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (56046341018 / 1000000000000) (56046341019 / 1000000000000), orderedInterval (29889819629 / 1000000000000) (29889819630 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (393907919768781 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-76789129790 / 1000000000000) (-76789128085 / 1000000000000), orderedInterval (24222974158 / 1000000000000) (24222975864 / 1000000000000)))) (orderedInterval (7049844079 / 1000000000000) (7049844124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (211844989330227 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-36273579404 / 1000000000000) (-36273579403 / 1000000000000), orderedInterval (-103123167912 / 1000000000000) (-103123167911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (575200355751681 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4743728411 / 1000000000000) (4743728413 / 1000000000000), orderedInterval (66350969500 / 1000000000000) (66350969502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (785386910387937 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40402231366 / 1000000000000) (40402280847 / 1000000000000), orderedInterval (-40227487602 / 1000000000000) (-40227438121 / 1000000000000)))) (orderedInterval (-4242694478 / 1000000000000) (-4242689210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (332092080231219 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (74436099417 / 1000000000000) (74436121171 / 1000000000000), orderedInterval (-46569798997 / 1000000000000) (-46569777243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1349935868938899 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-37077366729 / 1000000000000) (-37077302036 / 1000000000000), orderedInterval (22674374025 / 1000000000000) (22674438718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (901694598937341 / 4000000000000) 4 (IntervalRat.scale (363 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (734526258 / 1000000000000) (734526260 / 1000000000000), orderedInterval (53135656719 / 1000000000000) (53135656722 / 1000000000000)))) (orderedInterval (35427724782 / 1000000000000) (35427788370 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate308_chunkChecks4 :
    compactCertificate308.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate308.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate308_chunkChecks4_0
    compactCertificate308_chunkChecks4_1 compactCertificate308_chunkChecks4_2

theorem compactCertificate308_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate308.chunkCheck r b = true :=
  compactCertificate308.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate308_chunkChecks0
    · exact compactCertificate308_chunkChecks1
    · exact compactCertificate308_chunkChecks2
    · exact compactCertificate308_chunkChecks3
    · exact compactCertificate308_chunkChecks4)

theorem compactCertificate308_coefficient0 :
    compactCertificate308.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate308_coefficient1 :
    compactCertificate308.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate308_coefficient2 :
    compactCertificate308.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate308_coefficient3 :
    compactCertificate308.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate308_coefficient4 :
    compactCertificate308.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate308_coefficients : ∀ r : Fin 5,
    compactCertificate308.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate308_coefficient0
  · exact compactCertificate308_coefficient1
  · exact compactCertificate308_coefficient2
  · exact compactCertificate308_coefficient3
  · exact compactCertificate308_coefficient4

theorem compactCertificate308_lower : (1 : ℚ) ≤ compactCertificate308.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate308, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate308_proves {t : ℝ} (ht : t ∈ compactCertificate308.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate308.proves compactCertificate308_states compactCertificate308_chunks
    compactCertificate308_coefficients compactCertificate308_lower ht

end Erdos232
