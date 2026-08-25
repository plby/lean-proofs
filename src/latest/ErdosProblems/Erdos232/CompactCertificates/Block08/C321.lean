/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate321 : CompactCertificate where
  left := 193
  right := 194
  center := 387 / 2
  grid := fun i =>
    match i.val with
    | 0 => 62
    | 1 => 45
    | 2 => 73
    | 3 => 13
    | 4 => 36
    | 5 => 97
    | 6 => 71
    | 7 => 122
    | 8 => 90
    | 9 => 138
    | 10 => 80
    | 11 => 141
    | 12 => 132
    | 13 => 94
    | 14 => 107
    | 15 => 89
    | 16 => 79
    | 17 => 114
    | 18 => 63
    | 19 => 53
    | 20 => 33
    | 21 => 18
    | 22 => 49
    | 23 => 67
    | 24 => 28
    | 25 => 115
    | _ => 77
  point := fun i =>
    match i.val with
    | 0 => 387 / 2
    | 1 => 570124896837687 / 4000000000000
    | 2 => 184366677682071 / 800000000000
    | 3 => 166361022985509 / 4000000000000
    | 4 => 446869108352673 / 4000000000000
    | 5 => 1213336557598941 / 4000000000000
    | 6 => 893738216705733 / 4000000000000
    | 7 => 1531435667605209 / 4000000000000
    | 8 => 1128048581403531 / 4000000000000
    | 9 => 1730716614584613 / 4000000000000
    | 10 => 999229703321277 / 4000000000000
    | 11 => 1773150643349793 / 4000000000000
    | 12 => 1656707338069317 / 4000000000000
    | 13 => 1182304529298261 / 4000000000000
    | 14 => 1340607325058019 / 4000000000000
    | 15 => 1117658622293811 / 4000000000000
    | 16 => 987485287982031 / 4000000000000
    | 17 => 286211725545069 / 800000000000
    | 18 => 791676695355543 / 4000000000000
    | 19 => 671113102232223 / 4000000000000
    | 20 => 419951418596469 / 4000000000000
    | 21 => 225851269616523 / 4000000000000
    | 22 => 613230131338569 / 4000000000000
    | 23 => 837313317686313 / 4000000000000
    | 24 => 354048581403531 / 4000000000000
    | 25 => 1439187827215851 / 4000000000000
    | _ => 961310770767909 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-27196297186 / 1000000000000) (-27196294423 / 1000000000000), orderedInterval (50571680663 / 1000000000000) (50571683426 / 1000000000000))
    | 1 => (orderedInterval (-62229601411 / 1000000000000) (-62229596611 / 1000000000000), orderedInterval (24590110136 / 1000000000000) (24590114936 / 1000000000000))
    | 2 => (orderedInterval (-49617053513 / 1000000000000) (-49617048340 / 1000000000000), orderedInterval (17444030673 / 1000000000000) (17444035847 / 1000000000000))
    | 3 => (orderedInterval (-123623414652 / 1000000000000) (-123623414640 / 1000000000000), orderedInterval (-3319730757 / 1000000000000) (-3319730745 / 1000000000000))
    | 4 => (orderedInterval (-42360365259 / 1000000000000) (-42360353072 / 1000000000000), orderedInterval (62672462349 / 1000000000000) (62672474536 / 1000000000000))
    | 5 => (orderedInterval (26445153500 / 1000000000000) (26445159096 / 1000000000000), orderedInterval (-37452089492 / 1000000000000) (-37452083895 / 1000000000000))
    | 6 => (orderedInterval (-49070971017 / 1000000000000) (-49070971016 / 1000000000000), orderedInterval (-20896851189 / 1000000000000) (-20896851188 / 1000000000000))
    | 7 => (orderedInterval (14733787176 / 1000000000000) (14733787177 / 1000000000000), orderedInterval (38003405388 / 1000000000000) (38003405389 / 1000000000000))
    | 8 => (orderedInterval (2553098481 / 1000000000000) (2553098482 / 1000000000000), orderedInterval (47439176023 / 1000000000000) (47439176024 / 1000000000000))
    | 9 => (orderedInterval (-2894175474 / 1000000000000) (-2894175472 / 1000000000000), orderedInterval (38252115418 / 1000000000000) (38252115420 / 1000000000000))
    | 10 => (orderedInterval (-33855944180 / 1000000000000) (-33855920390 / 1000000000000), orderedInterval (37513959309 / 1000000000000) (37513983100 / 1000000000000))
    | 11 => (orderedInterval (-33913519619 / 1000000000000) (-33913519618 / 1000000000000), orderedInterval (-16873431245 / 1000000000000) (-16873431244 / 1000000000000))
    | 12 => (orderedInterval (10521581825 / 1000000000000) (10521581826 / 1000000000000), orderedInterval (37754607543 / 1000000000000) (37754607544 / 1000000000000))
    | 13 => (orderedInterval (40288756135 / 1000000000000) (40288756136 / 1000000000000), orderedInterval (22967499822 / 1000000000000) (22967499823 / 1000000000000))
    | 14 => (orderedInterval (9236929410 / 1000000000000) (9236929438 / 1000000000000), orderedInterval (-42606944953 / 1000000000000) (-42606944925 / 1000000000000))
    | 15 => (orderedInterval (-26867495615 / 1000000000000) (-26867495614 / 1000000000000), orderedInterval (-39404983983 / 1000000000000) (-39404983982 / 1000000000000))
    | 16 => (orderedInterval (25654393693 / 1000000000000) (25654396732 / 1000000000000), orderedInterval (-43876679508 / 1000000000000) (-43876676469 / 1000000000000))
    | 17 => (orderedInterval (16742815746 / 1000000000000) (16742815747 / 1000000000000), orderedInterval (38695028022 / 1000000000000) (38695028023 / 1000000000000))
    | 18 => (orderedInterval (-40031283985 / 1000000000000) (-40031283984 / 1000000000000), orderedInterval (-40074245285 / 1000000000000) (-40074245284 / 1000000000000))
    | 19 => (orderedInterval (-54416431725 / 1000000000000) (-54416414522 / 1000000000000), orderedInterval (29028307547 / 1000000000000) (29028324751 / 1000000000000))
    | 20 => (orderedInterval (-67237259989 / 1000000000000) (-67237241139 / 1000000000000), orderedInterval (39599519365 / 1000000000000) (39599538214 / 1000000000000))
    | 21 => (orderedInterval (68187495387 / 1000000000000) (68187495388 / 1000000000000), orderedInterval (80793822555 / 1000000000000) (80793822556 / 1000000000000))
    | 22 => (orderedInterval (-9889434485 / 1000000000000) (-9889434484 / 1000000000000), orderedInterval (-63644955695 / 1000000000000) (-63644955694 / 1000000000000))
    | 23 => (orderedInterval (20125971730 / 1000000000000) (20125972349 / 1000000000000), orderedInterval (-51392026333 / 1000000000000) (-51392025714 / 1000000000000))
    | 24 => (orderedInterval (82391826648 / 1000000000000) (82391826649 / 1000000000000), orderedInterval (19632890343 / 1000000000000) (19632890345 / 1000000000000))
    | 25 => (orderedInterval (27135304849 / 1000000000000) (27135314878 / 1000000000000), orderedInterval (-32178987211 / 1000000000000) (-32178977182 / 1000000000000))
    | _ => (orderedInterval (36562777204 / 1000000000000) (36562818274 / 1000000000000), orderedInterval (-36299385016 / 1000000000000) (-36299343946 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14271104574 / 1000000000000) (-14271103117 / 1000000000000)
      | 1 => orderedInterval (-2085401375 / 1000000000000) (-2085400508 / 1000000000000)
      | 2 => orderedInterval (-392745599 / 1000000000000) (-392745588 / 1000000000000)
      | 3 => orderedInterval (-6815193497 / 1000000000000) (-6815191657 / 1000000000000)
      | 4 => orderedInterval (3573129031 / 1000000000000) (3573129055 / 1000000000000)
      | 5 => orderedInterval (-1349690641 / 1000000000000) (-1349690448 / 1000000000000)
      | 6 => orderedInterval (7291739175 / 1000000000000) (7291740812 / 1000000000000)
      | 7 => orderedInterval (-2577161635 / 1000000000000) (-2577161564 / 1000000000000)
      | _ => orderedInterval (-8572332532 / 1000000000000) (-8572323956 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (21432770726 / 1000000000000) (21432772231 / 1000000000000)
      | 1 => orderedInterval (5502594440 / 1000000000000) (5502595347 / 1000000000000)
      | 2 => orderedInterval (-648311830 / 1000000000000) (-648311810 / 1000000000000)
      | 3 => orderedInterval (-17105196563 / 1000000000000) (-17105194127 / 1000000000000)
      | 4 => orderedInterval (2232145082 / 1000000000000) (2232145120 / 1000000000000)
      | 5 => orderedInterval (4378208450 / 1000000000000) (4378208700 / 1000000000000)
      | 6 => orderedInterval (5828776417 / 1000000000000) (5828777640 / 1000000000000)
      | 7 => orderedInterval (4969470469 / 1000000000000) (4969470542 / 1000000000000)
      | _ => orderedInterval (13383678425 / 1000000000000) (13383689590 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15113533661 / 1000000000000) (15113535237 / 1000000000000)
      | 1 => orderedInterval (5045056381 / 1000000000000) (5045057549 / 1000000000000)
      | 2 => orderedInterval (1651388097 / 1000000000000) (1651388131 / 1000000000000)
      | 3 => orderedInterval (26999387393 / 1000000000000) (26999390686 / 1000000000000)
      | 4 => orderedInterval (-7890637448 / 1000000000000) (-7890637384 / 1000000000000)
      | 5 => orderedInterval (1548542737 / 1000000000000) (1548543062 / 1000000000000)
      | 6 => orderedInterval (-8397690980 / 1000000000000) (-8397690017 / 1000000000000)
      | 7 => orderedInterval (1745783924 / 1000000000000) (1745784001 / 1000000000000)
      | _ => orderedInterval (18046163574 / 1000000000000) (18046178453 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-21943291066 / 1000000000000) (-21943289412 / 1000000000000)
      | 1 => orderedInterval (-10723261474 / 1000000000000) (-10723259795 / 1000000000000)
      | 2 => orderedInterval (5521777640 / 1000000000000) (5521777702 / 1000000000000)
      | 3 => orderedInterval (98710755649 / 1000000000000) (98710760209 / 1000000000000)
      | 4 => orderedInterval (-2136585796 / 1000000000000) (-2136585689 / 1000000000000)
      | 5 => orderedInterval (-10114133982 / 1000000000000) (-10114133557 / 1000000000000)
      | 6 => orderedInterval (-5948009937 / 1000000000000) (-5948009157 / 1000000000000)
      | 7 => orderedInterval (-5676311881 / 1000000000000) (-5676311799 / 1000000000000)
      | _ => orderedInterval (-29992532680 / 1000000000000) (-29992512421 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16581508712 / 1000000000000) (-16581506952 / 1000000000000)
      | 1 => orderedInterval (-11411101456 / 1000000000000) (-11411098903 / 1000000000000)
      | 2 => orderedInterval (-6743559406 / 1000000000000) (-6743559292 / 1000000000000)
      | 3 => orderedInterval (-127918214481 / 1000000000000) (-127918207874 / 1000000000000)
      | 4 => orderedInterval (16356478116 / 1000000000000) (16356478301 / 1000000000000)
      | 5 => orderedInterval (-124511933 / 1000000000000) (-124511370 / 1000000000000)
      | 6 => orderedInterval (8618176196 / 1000000000000) (8618176849 / 1000000000000)
      | 7 => orderedInterval (-1974494860 / 1000000000000) (-1974494771 / 1000000000000)
      | _ => orderedInterval (-42396035473 / 1000000000000) (-42396006896 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-25198761647 / 1000000000000) (-25198746971 / 1000000000000)
    | 1 => orderedInterval (39974135616 / 1000000000000) (39974153233 / 1000000000000)
    | 2 => orderedInterval (53861527339 / 1000000000000) (53861549718 / 1000000000000)
    | 3 => orderedInterval (17698406473 / 1000000000000) (17698436081 / 1000000000000)
    | _ => orderedInterval (-182174772009 / 1000000000000) (-182174730908 / 1000000000000)

theorem compactCertificate321_stateChecks0 :
    compactCertificate321.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (387 / 2)) (orderedInterval (-27196297186 / 1000000000000) (-27196294423 / 1000000000000), orderedInterval (50571680663 / 1000000000000) (50571683426 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (570124896837687 / 4000000000000)) (orderedInterval (-62229601411 / 1000000000000) (-62229596611 / 1000000000000), orderedInterval (24590110136 / 1000000000000) (24590114936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (184366677682071 / 800000000000)) (orderedInterval (-49617053513 / 1000000000000) (-49617048340 / 1000000000000), orderedInterval (17444030673 / 1000000000000) (17444035847 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks1 :
    compactCertificate321.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (166361022985509 / 4000000000000)) (orderedInterval (-123623414652 / 1000000000000) (-123623414640 / 1000000000000), orderedInterval (-3319730757 / 1000000000000) (-3319730745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (446869108352673 / 4000000000000)) (orderedInterval (-42360365259 / 1000000000000) (-42360353072 / 1000000000000), orderedInterval (62672462349 / 1000000000000) (62672474536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1213336557598941 / 4000000000000)) (orderedInterval (26445153500 / 1000000000000) (26445159096 / 1000000000000), orderedInterval (-37452089492 / 1000000000000) (-37452083895 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks2 :
    compactCertificate321.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (893738216705733 / 4000000000000)) (orderedInterval (-49070971017 / 1000000000000) (-49070971016 / 1000000000000), orderedInterval (-20896851189 / 1000000000000) (-20896851188 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1531435667605209 / 4000000000000)) (orderedInterval (14733787176 / 1000000000000) (14733787177 / 1000000000000), orderedInterval (38003405388 / 1000000000000) (38003405389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1128048581403531 / 4000000000000)) (orderedInterval (2553098481 / 1000000000000) (2553098482 / 1000000000000), orderedInterval (47439176023 / 1000000000000) (47439176024 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks3 :
    compactCertificate321.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1730716614584613 / 4000000000000)) (orderedInterval (-2894175474 / 1000000000000) (-2894175472 / 1000000000000), orderedInterval (38252115418 / 1000000000000) (38252115420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (999229703321277 / 4000000000000)) (orderedInterval (-33855944180 / 1000000000000) (-33855920390 / 1000000000000), orderedInterval (37513959309 / 1000000000000) (37513983100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1773150643349793 / 4000000000000)) (orderedInterval (-33913519619 / 1000000000000) (-33913519618 / 1000000000000), orderedInterval (-16873431245 / 1000000000000) (-16873431244 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks4 :
    compactCertificate321.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1656707338069317 / 4000000000000)) (orderedInterval (10521581825 / 1000000000000) (10521581826 / 1000000000000), orderedInterval (37754607543 / 1000000000000) (37754607544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1182304529298261 / 4000000000000)) (orderedInterval (40288756135 / 1000000000000) (40288756136 / 1000000000000), orderedInterval (22967499822 / 1000000000000) (22967499823 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1340607325058019 / 4000000000000)) (orderedInterval (9236929410 / 1000000000000) (9236929438 / 1000000000000), orderedInterval (-42606944953 / 1000000000000) (-42606944925 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks5 :
    compactCertificate321.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1117658622293811 / 4000000000000)) (orderedInterval (-26867495615 / 1000000000000) (-26867495614 / 1000000000000), orderedInterval (-39404983983 / 1000000000000) (-39404983982 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (987485287982031 / 4000000000000)) (orderedInterval (25654393693 / 1000000000000) (25654396732 / 1000000000000), orderedInterval (-43876679508 / 1000000000000) (-43876676469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (286211725545069 / 800000000000)) (orderedInterval (16742815746 / 1000000000000) (16742815747 / 1000000000000), orderedInterval (38695028022 / 1000000000000) (38695028023 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks6 :
    compactCertificate321.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (791676695355543 / 4000000000000)) (orderedInterval (-40031283985 / 1000000000000) (-40031283984 / 1000000000000), orderedInterval (-40074245285 / 1000000000000) (-40074245284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (671113102232223 / 4000000000000)) (orderedInterval (-54416431725 / 1000000000000) (-54416414522 / 1000000000000), orderedInterval (29028307547 / 1000000000000) (29028324751 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (419951418596469 / 4000000000000)) (orderedInterval (-67237259989 / 1000000000000) (-67237241139 / 1000000000000), orderedInterval (39599519365 / 1000000000000) (39599538214 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks7 :
    compactCertificate321.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (225851269616523 / 4000000000000)) (orderedInterval (68187495387 / 1000000000000) (68187495388 / 1000000000000), orderedInterval (80793822555 / 1000000000000) (80793822556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (613230131338569 / 4000000000000)) (orderedInterval (-9889434485 / 1000000000000) (-9889434484 / 1000000000000), orderedInterval (-63644955695 / 1000000000000) (-63644955694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (837313317686313 / 4000000000000)) (orderedInterval (20125971730 / 1000000000000) (20125972349 / 1000000000000), orderedInterval (-51392026333 / 1000000000000) (-51392025714 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_stateChecks8 :
    compactCertificate321.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (354048581403531 / 4000000000000)) (orderedInterval (82391826648 / 1000000000000) (82391826649 / 1000000000000), orderedInterval (19632890343 / 1000000000000) (19632890345 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1439187827215851 / 4000000000000)) (orderedInterval (27135304849 / 1000000000000) (27135314878 / 1000000000000), orderedInterval (-32178987211 / 1000000000000) (-32178977182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (961310770767909 / 4000000000000)) (orderedInterval (36562777204 / 1000000000000) (36562818274 / 1000000000000), orderedInterval (-36299385016 / 1000000000000) (-36299343946 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_states : ∀ j,
    BesselStateValid (compactCertificate321.point j) (compactCertificate321.state j) :=
  compactCertificate321.statesValid_of_checks3 compactCertificate321_stateChecks0
    compactCertificate321_stateChecks1 compactCertificate321_stateChecks2
    compactCertificate321_stateChecks3 compactCertificate321_stateChecks4
    compactCertificate321_stateChecks5 compactCertificate321_stateChecks6
    compactCertificate321_stateChecks7 compactCertificate321_stateChecks8

theorem compactCertificate321_chunkChecks0_0 :
    compactCertificate321.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (387 / 2) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27196297186 / 1000000000000) (-27196294423 / 1000000000000), orderedInterval (50571680663 / 1000000000000) (50571683426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (570124896837687 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62229601411 / 1000000000000) (-62229596611 / 1000000000000), orderedInterval (24590110136 / 1000000000000) (24590114936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (184366677682071 / 800000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49617053513 / 1000000000000) (-49617048340 / 1000000000000), orderedInterval (17444030673 / 1000000000000) (17444035847 / 1000000000000)))) (orderedInterval (-14271104574 / 1000000000000) (-14271103117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (166361022985509 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123623414652 / 1000000000000) (-123623414640 / 1000000000000), orderedInterval (-3319730757 / 1000000000000) (-3319730745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (446869108352673 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42360365259 / 1000000000000) (-42360353072 / 1000000000000), orderedInterval (62672462349 / 1000000000000) (62672474536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1213336557598941 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26445153500 / 1000000000000) (26445159096 / 1000000000000), orderedInterval (-37452089492 / 1000000000000) (-37452083895 / 1000000000000)))) (orderedInterval (-2085401375 / 1000000000000) (-2085400508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (893738216705733 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49070971017 / 1000000000000) (-49070971016 / 1000000000000), orderedInterval (-20896851189 / 1000000000000) (-20896851188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1531435667605209 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14733787176 / 1000000000000) (14733787177 / 1000000000000), orderedInterval (38003405388 / 1000000000000) (38003405389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1128048581403531 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2553098481 / 1000000000000) (2553098482 / 1000000000000), orderedInterval (47439176023 / 1000000000000) (47439176024 / 1000000000000)))) (orderedInterval (-392745599 / 1000000000000) (-392745588 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks0_1 :
    compactCertificate321.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1730716614584613 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2894175474 / 1000000000000) (-2894175472 / 1000000000000), orderedInterval (38252115418 / 1000000000000) (38252115420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (999229703321277 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33855944180 / 1000000000000) (-33855920390 / 1000000000000), orderedInterval (37513959309 / 1000000000000) (37513983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1773150643349793 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33913519619 / 1000000000000) (-33913519618 / 1000000000000), orderedInterval (-16873431245 / 1000000000000) (-16873431244 / 1000000000000)))) (orderedInterval (-6815193497 / 1000000000000) (-6815191657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1656707338069317 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10521581825 / 1000000000000) (10521581826 / 1000000000000), orderedInterval (37754607543 / 1000000000000) (37754607544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1182304529298261 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40288756135 / 1000000000000) (40288756136 / 1000000000000), orderedInterval (22967499822 / 1000000000000) (22967499823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1340607325058019 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9236929410 / 1000000000000) (9236929438 / 1000000000000), orderedInterval (-42606944953 / 1000000000000) (-42606944925 / 1000000000000)))) (orderedInterval (3573129031 / 1000000000000) (3573129055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1117658622293811 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867495615 / 1000000000000) (-26867495614 / 1000000000000), orderedInterval (-39404983983 / 1000000000000) (-39404983982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (987485287982031 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25654393693 / 1000000000000) (25654396732 / 1000000000000), orderedInterval (-43876679508 / 1000000000000) (-43876676469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (286211725545069 / 800000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16742815746 / 1000000000000) (16742815747 / 1000000000000), orderedInterval (38695028022 / 1000000000000) (38695028023 / 1000000000000)))) (orderedInterval (-1349690641 / 1000000000000) (-1349690448 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks0_2 :
    compactCertificate321.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (791676695355543 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40031283985 / 1000000000000) (-40031283984 / 1000000000000), orderedInterval (-40074245285 / 1000000000000) (-40074245284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (671113102232223 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54416431725 / 1000000000000) (-54416414522 / 1000000000000), orderedInterval (29028307547 / 1000000000000) (29028324751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (419951418596469 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67237259989 / 1000000000000) (-67237241139 / 1000000000000), orderedInterval (39599519365 / 1000000000000) (39599538214 / 1000000000000)))) (orderedInterval (7291739175 / 1000000000000) (7291740812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (225851269616523 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68187495387 / 1000000000000) (68187495388 / 1000000000000), orderedInterval (80793822555 / 1000000000000) (80793822556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (613230131338569 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9889434485 / 1000000000000) (-9889434484 / 1000000000000), orderedInterval (-63644955695 / 1000000000000) (-63644955694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (837313317686313 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20125971730 / 1000000000000) (20125972349 / 1000000000000), orderedInterval (-51392026333 / 1000000000000) (-51392025714 / 1000000000000)))) (orderedInterval (-2577161635 / 1000000000000) (-2577161564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (354048581403531 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82391826648 / 1000000000000) (82391826649 / 1000000000000), orderedInterval (19632890343 / 1000000000000) (19632890345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1439187827215851 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27135304849 / 1000000000000) (27135314878 / 1000000000000), orderedInterval (-32178987211 / 1000000000000) (-32178977182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (961310770767909 / 4000000000000) 0 (IntervalRat.scale (387 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36562777204 / 1000000000000) (36562818274 / 1000000000000), orderedInterval (-36299385016 / 1000000000000) (-36299343946 / 1000000000000)))) (orderedInterval (-8572332532 / 1000000000000) (-8572323956 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks0 :
    compactCertificate321.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate321.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate321_chunkChecks0_0
    compactCertificate321_chunkChecks0_1 compactCertificate321_chunkChecks0_2

theorem compactCertificate321_chunkChecks1_0 :
    compactCertificate321.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (387 / 2) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27196297186 / 1000000000000) (-27196294423 / 1000000000000), orderedInterval (50571680663 / 1000000000000) (50571683426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (570124896837687 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62229601411 / 1000000000000) (-62229596611 / 1000000000000), orderedInterval (24590110136 / 1000000000000) (24590114936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (184366677682071 / 800000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49617053513 / 1000000000000) (-49617048340 / 1000000000000), orderedInterval (17444030673 / 1000000000000) (17444035847 / 1000000000000)))) (orderedInterval (21432770726 / 1000000000000) (21432772231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (166361022985509 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123623414652 / 1000000000000) (-123623414640 / 1000000000000), orderedInterval (-3319730757 / 1000000000000) (-3319730745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (446869108352673 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42360365259 / 1000000000000) (-42360353072 / 1000000000000), orderedInterval (62672462349 / 1000000000000) (62672474536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1213336557598941 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26445153500 / 1000000000000) (26445159096 / 1000000000000), orderedInterval (-37452089492 / 1000000000000) (-37452083895 / 1000000000000)))) (orderedInterval (5502594440 / 1000000000000) (5502595347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (893738216705733 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49070971017 / 1000000000000) (-49070971016 / 1000000000000), orderedInterval (-20896851189 / 1000000000000) (-20896851188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1531435667605209 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14733787176 / 1000000000000) (14733787177 / 1000000000000), orderedInterval (38003405388 / 1000000000000) (38003405389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1128048581403531 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2553098481 / 1000000000000) (2553098482 / 1000000000000), orderedInterval (47439176023 / 1000000000000) (47439176024 / 1000000000000)))) (orderedInterval (-648311830 / 1000000000000) (-648311810 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks1_1 :
    compactCertificate321.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1730716614584613 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2894175474 / 1000000000000) (-2894175472 / 1000000000000), orderedInterval (38252115418 / 1000000000000) (38252115420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (999229703321277 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33855944180 / 1000000000000) (-33855920390 / 1000000000000), orderedInterval (37513959309 / 1000000000000) (37513983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1773150643349793 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33913519619 / 1000000000000) (-33913519618 / 1000000000000), orderedInterval (-16873431245 / 1000000000000) (-16873431244 / 1000000000000)))) (orderedInterval (-17105196563 / 1000000000000) (-17105194127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1656707338069317 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10521581825 / 1000000000000) (10521581826 / 1000000000000), orderedInterval (37754607543 / 1000000000000) (37754607544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1182304529298261 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40288756135 / 1000000000000) (40288756136 / 1000000000000), orderedInterval (22967499822 / 1000000000000) (22967499823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1340607325058019 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9236929410 / 1000000000000) (9236929438 / 1000000000000), orderedInterval (-42606944953 / 1000000000000) (-42606944925 / 1000000000000)))) (orderedInterval (2232145082 / 1000000000000) (2232145120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1117658622293811 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867495615 / 1000000000000) (-26867495614 / 1000000000000), orderedInterval (-39404983983 / 1000000000000) (-39404983982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (987485287982031 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25654393693 / 1000000000000) (25654396732 / 1000000000000), orderedInterval (-43876679508 / 1000000000000) (-43876676469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (286211725545069 / 800000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16742815746 / 1000000000000) (16742815747 / 1000000000000), orderedInterval (38695028022 / 1000000000000) (38695028023 / 1000000000000)))) (orderedInterval (4378208450 / 1000000000000) (4378208700 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks1_2 :
    compactCertificate321.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (791676695355543 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40031283985 / 1000000000000) (-40031283984 / 1000000000000), orderedInterval (-40074245285 / 1000000000000) (-40074245284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (671113102232223 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54416431725 / 1000000000000) (-54416414522 / 1000000000000), orderedInterval (29028307547 / 1000000000000) (29028324751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (419951418596469 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67237259989 / 1000000000000) (-67237241139 / 1000000000000), orderedInterval (39599519365 / 1000000000000) (39599538214 / 1000000000000)))) (orderedInterval (5828776417 / 1000000000000) (5828777640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (225851269616523 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68187495387 / 1000000000000) (68187495388 / 1000000000000), orderedInterval (80793822555 / 1000000000000) (80793822556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (613230131338569 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9889434485 / 1000000000000) (-9889434484 / 1000000000000), orderedInterval (-63644955695 / 1000000000000) (-63644955694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (837313317686313 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20125971730 / 1000000000000) (20125972349 / 1000000000000), orderedInterval (-51392026333 / 1000000000000) (-51392025714 / 1000000000000)))) (orderedInterval (4969470469 / 1000000000000) (4969470542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (354048581403531 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82391826648 / 1000000000000) (82391826649 / 1000000000000), orderedInterval (19632890343 / 1000000000000) (19632890345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1439187827215851 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27135304849 / 1000000000000) (27135314878 / 1000000000000), orderedInterval (-32178987211 / 1000000000000) (-32178977182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (961310770767909 / 4000000000000) 1 (IntervalRat.scale (387 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36562777204 / 1000000000000) (36562818274 / 1000000000000), orderedInterval (-36299385016 / 1000000000000) (-36299343946 / 1000000000000)))) (orderedInterval (13383678425 / 1000000000000) (13383689590 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks1 :
    compactCertificate321.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate321.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate321_chunkChecks1_0
    compactCertificate321_chunkChecks1_1 compactCertificate321_chunkChecks1_2

theorem compactCertificate321_chunkChecks2_0 :
    compactCertificate321.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (387 / 2) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27196297186 / 1000000000000) (-27196294423 / 1000000000000), orderedInterval (50571680663 / 1000000000000) (50571683426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (570124896837687 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62229601411 / 1000000000000) (-62229596611 / 1000000000000), orderedInterval (24590110136 / 1000000000000) (24590114936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (184366677682071 / 800000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49617053513 / 1000000000000) (-49617048340 / 1000000000000), orderedInterval (17444030673 / 1000000000000) (17444035847 / 1000000000000)))) (orderedInterval (15113533661 / 1000000000000) (15113535237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (166361022985509 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123623414652 / 1000000000000) (-123623414640 / 1000000000000), orderedInterval (-3319730757 / 1000000000000) (-3319730745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (446869108352673 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42360365259 / 1000000000000) (-42360353072 / 1000000000000), orderedInterval (62672462349 / 1000000000000) (62672474536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1213336557598941 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26445153500 / 1000000000000) (26445159096 / 1000000000000), orderedInterval (-37452089492 / 1000000000000) (-37452083895 / 1000000000000)))) (orderedInterval (5045056381 / 1000000000000) (5045057549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (893738216705733 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49070971017 / 1000000000000) (-49070971016 / 1000000000000), orderedInterval (-20896851189 / 1000000000000) (-20896851188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1531435667605209 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14733787176 / 1000000000000) (14733787177 / 1000000000000), orderedInterval (38003405388 / 1000000000000) (38003405389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1128048581403531 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2553098481 / 1000000000000) (2553098482 / 1000000000000), orderedInterval (47439176023 / 1000000000000) (47439176024 / 1000000000000)))) (orderedInterval (1651388097 / 1000000000000) (1651388131 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks2_1 :
    compactCertificate321.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1730716614584613 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2894175474 / 1000000000000) (-2894175472 / 1000000000000), orderedInterval (38252115418 / 1000000000000) (38252115420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (999229703321277 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33855944180 / 1000000000000) (-33855920390 / 1000000000000), orderedInterval (37513959309 / 1000000000000) (37513983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1773150643349793 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33913519619 / 1000000000000) (-33913519618 / 1000000000000), orderedInterval (-16873431245 / 1000000000000) (-16873431244 / 1000000000000)))) (orderedInterval (26999387393 / 1000000000000) (26999390686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1656707338069317 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10521581825 / 1000000000000) (10521581826 / 1000000000000), orderedInterval (37754607543 / 1000000000000) (37754607544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1182304529298261 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40288756135 / 1000000000000) (40288756136 / 1000000000000), orderedInterval (22967499822 / 1000000000000) (22967499823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1340607325058019 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9236929410 / 1000000000000) (9236929438 / 1000000000000), orderedInterval (-42606944953 / 1000000000000) (-42606944925 / 1000000000000)))) (orderedInterval (-7890637448 / 1000000000000) (-7890637384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1117658622293811 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867495615 / 1000000000000) (-26867495614 / 1000000000000), orderedInterval (-39404983983 / 1000000000000) (-39404983982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (987485287982031 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25654393693 / 1000000000000) (25654396732 / 1000000000000), orderedInterval (-43876679508 / 1000000000000) (-43876676469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (286211725545069 / 800000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16742815746 / 1000000000000) (16742815747 / 1000000000000), orderedInterval (38695028022 / 1000000000000) (38695028023 / 1000000000000)))) (orderedInterval (1548542737 / 1000000000000) (1548543062 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks2_2 :
    compactCertificate321.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (791676695355543 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40031283985 / 1000000000000) (-40031283984 / 1000000000000), orderedInterval (-40074245285 / 1000000000000) (-40074245284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (671113102232223 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54416431725 / 1000000000000) (-54416414522 / 1000000000000), orderedInterval (29028307547 / 1000000000000) (29028324751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (419951418596469 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67237259989 / 1000000000000) (-67237241139 / 1000000000000), orderedInterval (39599519365 / 1000000000000) (39599538214 / 1000000000000)))) (orderedInterval (-8397690980 / 1000000000000) (-8397690017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (225851269616523 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68187495387 / 1000000000000) (68187495388 / 1000000000000), orderedInterval (80793822555 / 1000000000000) (80793822556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (613230131338569 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9889434485 / 1000000000000) (-9889434484 / 1000000000000), orderedInterval (-63644955695 / 1000000000000) (-63644955694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (837313317686313 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20125971730 / 1000000000000) (20125972349 / 1000000000000), orderedInterval (-51392026333 / 1000000000000) (-51392025714 / 1000000000000)))) (orderedInterval (1745783924 / 1000000000000) (1745784001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (354048581403531 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82391826648 / 1000000000000) (82391826649 / 1000000000000), orderedInterval (19632890343 / 1000000000000) (19632890345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1439187827215851 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27135304849 / 1000000000000) (27135314878 / 1000000000000), orderedInterval (-32178987211 / 1000000000000) (-32178977182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (961310770767909 / 4000000000000) 2 (IntervalRat.scale (387 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36562777204 / 1000000000000) (36562818274 / 1000000000000), orderedInterval (-36299385016 / 1000000000000) (-36299343946 / 1000000000000)))) (orderedInterval (18046163574 / 1000000000000) (18046178453 / 1000000000000))) = true
  rfl'

theorem compactCertificate321_chunkChecks2 :
    compactCertificate321.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate321.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate321_chunkChecks2_0
    compactCertificate321_chunkChecks2_1 compactCertificate321_chunkChecks2_2

theorem compactCertificate321_chunkChecks3_0 :
    compactCertificate321.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (387 / 2) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27196297186 / 1000000000000) (-27196294423 / 1000000000000), orderedInterval (50571680663 / 1000000000000) (50571683426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (570124896837687 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62229601411 / 1000000000000) (-62229596611 / 1000000000000), orderedInterval (24590110136 / 1000000000000) (24590114936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (184366677682071 / 800000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49617053513 / 1000000000000) (-49617048340 / 1000000000000), orderedInterval (17444030673 / 1000000000000) (17444035847 / 1000000000000)))) (orderedInterval (-21943291066 / 1000000000000) (-21943289412 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (166361022985509 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123623414652 / 1000000000000) (-123623414640 / 1000000000000), orderedInterval (-3319730757 / 1000000000000) (-3319730745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (446869108352673 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42360365259 / 1000000000000) (-42360353072 / 1000000000000), orderedInterval (62672462349 / 1000000000000) (62672474536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1213336557598941 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26445153500 / 1000000000000) (26445159096 / 1000000000000), orderedInterval (-37452089492 / 1000000000000) (-37452083895 / 1000000000000)))) (orderedInterval (-10723261474 / 1000000000000) (-10723259795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (893738216705733 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49070971017 / 1000000000000) (-49070971016 / 1000000000000), orderedInterval (-20896851189 / 1000000000000) (-20896851188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1531435667605209 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14733787176 / 1000000000000) (14733787177 / 1000000000000), orderedInterval (38003405388 / 1000000000000) (38003405389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1128048581403531 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2553098481 / 1000000000000) (2553098482 / 1000000000000), orderedInterval (47439176023 / 1000000000000) (47439176024 / 1000000000000)))) (orderedInterval (5521777640 / 1000000000000) (5521777702 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate321_chunkChecks3_1 :
    compactCertificate321.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1730716614584613 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2894175474 / 1000000000000) (-2894175472 / 1000000000000), orderedInterval (38252115418 / 1000000000000) (38252115420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (999229703321277 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33855944180 / 1000000000000) (-33855920390 / 1000000000000), orderedInterval (37513959309 / 1000000000000) (37513983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1773150643349793 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33913519619 / 1000000000000) (-33913519618 / 1000000000000), orderedInterval (-16873431245 / 1000000000000) (-16873431244 / 1000000000000)))) (orderedInterval (98710755649 / 1000000000000) (98710760209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1656707338069317 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10521581825 / 1000000000000) (10521581826 / 1000000000000), orderedInterval (37754607543 / 1000000000000) (37754607544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1182304529298261 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40288756135 / 1000000000000) (40288756136 / 1000000000000), orderedInterval (22967499822 / 1000000000000) (22967499823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1340607325058019 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9236929410 / 1000000000000) (9236929438 / 1000000000000), orderedInterval (-42606944953 / 1000000000000) (-42606944925 / 1000000000000)))) (orderedInterval (-2136585796 / 1000000000000) (-2136585689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1117658622293811 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867495615 / 1000000000000) (-26867495614 / 1000000000000), orderedInterval (-39404983983 / 1000000000000) (-39404983982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (987485287982031 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25654393693 / 1000000000000) (25654396732 / 1000000000000), orderedInterval (-43876679508 / 1000000000000) (-43876676469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (286211725545069 / 800000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16742815746 / 1000000000000) (16742815747 / 1000000000000), orderedInterval (38695028022 / 1000000000000) (38695028023 / 1000000000000)))) (orderedInterval (-10114133982 / 1000000000000) (-10114133557 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate321_chunkChecks3_2 :
    compactCertificate321.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (791676695355543 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40031283985 / 1000000000000) (-40031283984 / 1000000000000), orderedInterval (-40074245285 / 1000000000000) (-40074245284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (671113102232223 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54416431725 / 1000000000000) (-54416414522 / 1000000000000), orderedInterval (29028307547 / 1000000000000) (29028324751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (419951418596469 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67237259989 / 1000000000000) (-67237241139 / 1000000000000), orderedInterval (39599519365 / 1000000000000) (39599538214 / 1000000000000)))) (orderedInterval (-5948009937 / 1000000000000) (-5948009157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (225851269616523 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68187495387 / 1000000000000) (68187495388 / 1000000000000), orderedInterval (80793822555 / 1000000000000) (80793822556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (613230131338569 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9889434485 / 1000000000000) (-9889434484 / 1000000000000), orderedInterval (-63644955695 / 1000000000000) (-63644955694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (837313317686313 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20125971730 / 1000000000000) (20125972349 / 1000000000000), orderedInterval (-51392026333 / 1000000000000) (-51392025714 / 1000000000000)))) (orderedInterval (-5676311881 / 1000000000000) (-5676311799 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (354048581403531 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82391826648 / 1000000000000) (82391826649 / 1000000000000), orderedInterval (19632890343 / 1000000000000) (19632890345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1439187827215851 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27135304849 / 1000000000000) (27135314878 / 1000000000000), orderedInterval (-32178987211 / 1000000000000) (-32178977182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (961310770767909 / 4000000000000) 3 (IntervalRat.scale (387 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36562777204 / 1000000000000) (36562818274 / 1000000000000), orderedInterval (-36299385016 / 1000000000000) (-36299343946 / 1000000000000)))) (orderedInterval (-29992532680 / 1000000000000) (-29992512421 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate321_chunkChecks3 :
    compactCertificate321.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate321.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate321_chunkChecks3_0
    compactCertificate321_chunkChecks3_1 compactCertificate321_chunkChecks3_2

theorem compactCertificate321_chunkChecks4_0 :
    compactCertificate321.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (387 / 2) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27196297186 / 1000000000000) (-27196294423 / 1000000000000), orderedInterval (50571680663 / 1000000000000) (50571683426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (570124896837687 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62229601411 / 1000000000000) (-62229596611 / 1000000000000), orderedInterval (24590110136 / 1000000000000) (24590114936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (184366677682071 / 800000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49617053513 / 1000000000000) (-49617048340 / 1000000000000), orderedInterval (17444030673 / 1000000000000) (17444035847 / 1000000000000)))) (orderedInterval (-16581508712 / 1000000000000) (-16581506952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (166361022985509 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123623414652 / 1000000000000) (-123623414640 / 1000000000000), orderedInterval (-3319730757 / 1000000000000) (-3319730745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (446869108352673 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42360365259 / 1000000000000) (-42360353072 / 1000000000000), orderedInterval (62672462349 / 1000000000000) (62672474536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1213336557598941 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26445153500 / 1000000000000) (26445159096 / 1000000000000), orderedInterval (-37452089492 / 1000000000000) (-37452083895 / 1000000000000)))) (orderedInterval (-11411101456 / 1000000000000) (-11411098903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (893738216705733 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49070971017 / 1000000000000) (-49070971016 / 1000000000000), orderedInterval (-20896851189 / 1000000000000) (-20896851188 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1531435667605209 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14733787176 / 1000000000000) (14733787177 / 1000000000000), orderedInterval (38003405388 / 1000000000000) (38003405389 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1128048581403531 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (2553098481 / 1000000000000) (2553098482 / 1000000000000), orderedInterval (47439176023 / 1000000000000) (47439176024 / 1000000000000)))) (orderedInterval (-6743559406 / 1000000000000) (-6743559292 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate321_chunkChecks4_1 :
    compactCertificate321.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1730716614584613 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-2894175474 / 1000000000000) (-2894175472 / 1000000000000), orderedInterval (38252115418 / 1000000000000) (38252115420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (999229703321277 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33855944180 / 1000000000000) (-33855920390 / 1000000000000), orderedInterval (37513959309 / 1000000000000) (37513983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1773150643349793 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33913519619 / 1000000000000) (-33913519618 / 1000000000000), orderedInterval (-16873431245 / 1000000000000) (-16873431244 / 1000000000000)))) (orderedInterval (-127918214481 / 1000000000000) (-127918207874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1656707338069317 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10521581825 / 1000000000000) (10521581826 / 1000000000000), orderedInterval (37754607543 / 1000000000000) (37754607544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1182304529298261 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40288756135 / 1000000000000) (40288756136 / 1000000000000), orderedInterval (22967499822 / 1000000000000) (22967499823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1340607325058019 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9236929410 / 1000000000000) (9236929438 / 1000000000000), orderedInterval (-42606944953 / 1000000000000) (-42606944925 / 1000000000000)))) (orderedInterval (16356478116 / 1000000000000) (16356478301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1117658622293811 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26867495615 / 1000000000000) (-26867495614 / 1000000000000), orderedInterval (-39404983983 / 1000000000000) (-39404983982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (987485287982031 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25654393693 / 1000000000000) (25654396732 / 1000000000000), orderedInterval (-43876679508 / 1000000000000) (-43876676469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (286211725545069 / 800000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16742815746 / 1000000000000) (16742815747 / 1000000000000), orderedInterval (38695028022 / 1000000000000) (38695028023 / 1000000000000)))) (orderedInterval (-124511933 / 1000000000000) (-124511370 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate321_chunkChecks4_2 :
    compactCertificate321.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (791676695355543 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40031283985 / 1000000000000) (-40031283984 / 1000000000000), orderedInterval (-40074245285 / 1000000000000) (-40074245284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (671113102232223 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54416431725 / 1000000000000) (-54416414522 / 1000000000000), orderedInterval (29028307547 / 1000000000000) (29028324751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (419951418596469 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-67237259989 / 1000000000000) (-67237241139 / 1000000000000), orderedInterval (39599519365 / 1000000000000) (39599538214 / 1000000000000)))) (orderedInterval (8618176196 / 1000000000000) (8618176849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (225851269616523 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68187495387 / 1000000000000) (68187495388 / 1000000000000), orderedInterval (80793822555 / 1000000000000) (80793822556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (613230131338569 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9889434485 / 1000000000000) (-9889434484 / 1000000000000), orderedInterval (-63644955695 / 1000000000000) (-63644955694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (837313317686313 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20125971730 / 1000000000000) (20125972349 / 1000000000000), orderedInterval (-51392026333 / 1000000000000) (-51392025714 / 1000000000000)))) (orderedInterval (-1974494860 / 1000000000000) (-1974494771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (354048581403531 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82391826648 / 1000000000000) (82391826649 / 1000000000000), orderedInterval (19632890343 / 1000000000000) (19632890345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1439187827215851 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27135304849 / 1000000000000) (27135314878 / 1000000000000), orderedInterval (-32178987211 / 1000000000000) (-32178977182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (961310770767909 / 4000000000000) 4 (IntervalRat.scale (387 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36562777204 / 1000000000000) (36562818274 / 1000000000000), orderedInterval (-36299385016 / 1000000000000) (-36299343946 / 1000000000000)))) (orderedInterval (-42396035473 / 1000000000000) (-42396006896 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate321_chunkChecks4 :
    compactCertificate321.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate321.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate321_chunkChecks4_0
    compactCertificate321_chunkChecks4_1 compactCertificate321_chunkChecks4_2

theorem compactCertificate321_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate321.chunkCheck r b = true :=
  compactCertificate321.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate321_chunkChecks0
    · exact compactCertificate321_chunkChecks1
    · exact compactCertificate321_chunkChecks2
    · exact compactCertificate321_chunkChecks3
    · exact compactCertificate321_chunkChecks4)

theorem compactCertificate321_coefficient0 :
    compactCertificate321.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate321_coefficient1 :
    compactCertificate321.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate321_coefficient2 :
    compactCertificate321.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate321_coefficient3 :
    compactCertificate321.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate321_coefficient4 :
    compactCertificate321.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate321_coefficients : ∀ r : Fin 5,
    compactCertificate321.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate321_coefficient0
  · exact compactCertificate321_coefficient1
  · exact compactCertificate321_coefficient2
  · exact compactCertificate321_coefficient3
  · exact compactCertificate321_coefficient4

theorem compactCertificate321_lower : (1 : ℚ) ≤ compactCertificate321.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate321, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate321_proves {t : ℝ} (ht : t ∈ compactCertificate321.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate321.proves compactCertificate321_states compactCertificate321_chunks
    compactCertificate321_coefficients compactCertificate321_lower ht

end Erdos232
