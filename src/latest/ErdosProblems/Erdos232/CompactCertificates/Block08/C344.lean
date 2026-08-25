/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate344 : CompactCertificate where
  left := 216
  right := 433 / 2
  center := 865 / 4
  grid := fun i =>
    match i.val with
    | 0 => 69
    | 1 => 51
    | 2 => 82
    | 3 => 15
    | 4 => 40
    | 5 => 108
    | 6 => 80
    | 7 => 136
    | 8 => 100
    | 9 => 154
    | 10 => 89
    | 11 => 158
    | 12 => 147
    | 13 => 105
    | 14 => 119
    | 15 => 99
    | 16 => 88
    | 17 => 127
    | 18 => 70
    | 19 => 60
    | 20 => 37
    | 21 => 20
    | 22 => 55
    | 23 => 75
    | 24 => 32
    | 25 => 128
    | _ => 86
  point := fun i =>
    match i.val with
    | 0 => 865 / 4
    | 1 => 254862033986873 / 1600000000000
    | 2 => 82417145320409 / 320000000000
    | 3 => 74368105882411 / 1600000000000
    | 4 => 199763193139567 / 1600000000000
    | 5 => 542395928849139 / 1600000000000
    | 6 => 399526386279307 / 1600000000000
    | 7 => 684595272598711 / 1600000000000
    | 8 => 504269779283749 / 1600000000000
    | 9 => 773679520214827 / 1600000000000
    | 10 => 446684079262483 / 1600000000000
    | 11 => 792648737208047 / 1600000000000
    | 12 => 740595269989643 / 1600000000000
    | 13 => 528523730151419 / 1600000000000
    | 14 => 599289579418701 / 1600000000000
    | 15 => 499625172239869 / 1600000000000
    | 16 => 441433991785249 / 1600000000000
    | 17 => 127944776535651 / 320000000000
    | 18 => 353901985262297 / 1600000000000
    | 19 => 300006632264017 / 1600000000000
    | 20 => 187730220716251 / 1600000000000
    | 21 => 100961937063717 / 1600000000000
    | 22 => 274131299022151 / 1600000000000
    | 23 => 374302852609127 / 1600000000000
    | 24 => 158269779283749 / 1600000000000
    | 25 => 643357865913029 / 1600000000000
    | _ => 429733238612011 / 1600000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-14206775281 / 1000000000000) (-14206775280 / 1000000000000), orderedInterval (-52332033385 / 1000000000000) (-52332033384 / 1000000000000))
    | 1 => (orderedInterval (9312302324 / 1000000000000) (9312302365 / 1000000000000), orderedInterval (-62558737380 / 1000000000000) (-62558737339 / 1000000000000))
    | 2 => (orderedInterval (33076746721 / 1000000000000) (33076746722 / 1000000000000), orderedInterval (37053502888 / 1000000000000) (37053502889 / 1000000000000))
    | 3 => (orderedInterval (-16201493921 / 1000000000000) (-16201493919 / 1000000000000), orderedInterval (-115734719381 / 1000000000000) (-115734719379 / 1000000000000))
    | 4 => (orderedInterval (-1950125938 / 1000000000000) (-1950125930 / 1000000000000), orderedInterval (71388713209 / 1000000000000) (71388713218 / 1000000000000))
    | 5 => (orderedInterval (20412993427 / 1000000000000) (20412993428 / 1000000000000), orderedInterval (38196314491 / 1000000000000) (38196314492 / 1000000000000))
    | 6 => (orderedInterval (-37549113569 / 1000000000000) (-37549053188 / 1000000000000), orderedInterval (33832577022 / 1000000000000) (33832637403 / 1000000000000))
    | 7 => (orderedInterval (38015315539 / 1000000000000) (38015315570 / 1000000000000), orderedInterval (6490789763 / 1000000000000) (6490789793 / 1000000000000))
    | 8 => (orderedInterval (43825275048 / 1000000000000) (43825277484 / 1000000000000), orderedInterval (-10033301709 / 1000000000000) (-10033299274 / 1000000000000))
    | 9 => (orderedInterval (18329522591 / 1000000000000) (18329522592 / 1000000000000), orderedInterval (31295323861 / 1000000000000) (31295323862 / 1000000000000))
    | 10 => (orderedInterval (-16855788776 / 1000000000000) (-16855788775 / 1000000000000), orderedInterval (-44648948661 / 1000000000000) (-44648948660 / 1000000000000))
    | 11 => (orderedInterval (-6454189795 / 1000000000000) (-6454189790 / 1000000000000), orderedInterval (35268277996 / 1000000000000) (35268278001 / 1000000000000))
    | 12 => (orderedInterval (-35719966023 / 1000000000000) (-35719957040 / 1000000000000), orderedInterval (10011166082 / 1000000000000) (10011175064 / 1000000000000))
    | 13 => (orderedInterval (-41592702519 / 1000000000000) (-41592702517 / 1000000000000), orderedInterval (-13982843892 / 1000000000000) (-13982843891 / 1000000000000))
    | 14 => (orderedInterval (-41097513960 / 1000000000000) (-41097513882 / 1000000000000), orderedInterval (-3209804208 / 1000000000000) (-3209804130 / 1000000000000))
    | 15 => (orderedInterval (-40413198523 / 1000000000000) (-40413171639 / 1000000000000), orderedInterval (20201340413 / 1000000000000) (20201367298 / 1000000000000))
    | 16 => (orderedInterval (10531458708 / 1000000000000) (10531458709 / 1000000000000), orderedInterval (46848308062 / 1000000000000) (46848308063 / 1000000000000))
    | 17 => (orderedInterval (-39832330483 / 1000000000000) (-39832329895 / 1000000000000), orderedInterval (2420593998 / 1000000000000) (2420594586 / 1000000000000))
    | 18 => (orderedInterval (47303213530 / 1000000000000) (47303236483 / 1000000000000), orderedInterval (-25416526921 / 1000000000000) (-25416503967 / 1000000000000))
    | 19 => (orderedInterval (-11957522278 / 1000000000000) (-11957522200 / 1000000000000), orderedInterval (57060467259 / 1000000000000) (57060467337 / 1000000000000))
    | 20 => (orderedInterval (-70238177412 / 1000000000000) (-70238175403 / 1000000000000), orderedInterval (22489056629 / 1000000000000) (22489058637 / 1000000000000))
    | 21 => (orderedInterval (87263886815 / 1000000000000) (87263886816 / 1000000000000), orderedInterval (49045094601 / 1000000000000) (49045094602 / 1000000000000))
    | 22 => (orderedInterval (37894441041 / 1000000000000) (37894459906 / 1000000000000), orderedInterval (-47857023613 / 1000000000000) (-47857004749 / 1000000000000))
    | 23 => (orderedInterval (40710236952 / 1000000000000) (40710341657 / 1000000000000), orderedInterval (-32705678733 / 1000000000000) (-32705574028 / 1000000000000))
    | 24 => (orderedInterval (-59102477433 / 1000000000000) (-59102372141 / 1000000000000), orderedInterval (54545242752 / 1000000000000) (54545348044 / 1000000000000))
    | 25 => (orderedInterval (27409099285 / 1000000000000) (27409099286 / 1000000000000), orderedInterval (28810050782 / 1000000000000) (28810050783 / 1000000000000))
    | _ => (orderedInterval (-35220741896 / 1000000000000) (-35220699172 / 1000000000000), orderedInterval (33677876791 / 1000000000000) (33677919515 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-3603314596 / 1000000000000) (-3603314579 / 1000000000000)
      | 1 => orderedInterval (-1346580169 / 1000000000000) (-1346580142 / 1000000000000)
      | 2 => orderedInterval (-113374007 / 1000000000000) (-113373935 / 1000000000000)
      | 3 => orderedInterval (-5423311246 / 1000000000000) (-5423311159 / 1000000000000)
      | 4 => orderedInterval (-3080292619 / 1000000000000) (-3080292430 / 1000000000000)
      | 5 => orderedInterval (-2089223675 / 1000000000000) (-2089223328 / 1000000000000)
      | 6 => orderedInterval (-9173257693 / 1000000000000) (-9173253898 / 1000000000000)
      | 7 => orderedInterval (-5591038858 / 1000000000000) (-5591030379 / 1000000000000)
      | _ => orderedInterval (4020898926 / 1000000000000) (4020907638 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-18582327404 / 1000000000000) (-18582327386 / 1000000000000)
      | 1 => orderedInterval (-2481889717 / 1000000000000) (-2481889686 / 1000000000000)
      | 2 => orderedInterval (-749523722 / 1000000000000) (-749523612 / 1000000000000)
      | 3 => orderedInterval (-5219490897 / 1000000000000) (-5219490717 / 1000000000000)
      | 4 => orderedInterval (-2378496548 / 1000000000000) (-2378496157 / 1000000000000)
      | 5 => orderedInterval (-2968996619 / 1000000000000) (-2968996112 / 1000000000000)
      | 6 => orderedInterval (1753646264 / 1000000000000) (1753650108 / 1000000000000)
      | 7 => orderedInterval (3307499146 / 1000000000000) (3307508190 / 1000000000000)
      | _ => orderedInterval (-12058332992 / 1000000000000) (-12058322661 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (2916676448 / 1000000000000) (2916676469 / 1000000000000)
      | 1 => orderedInterval (3593191871 / 1000000000000) (3593191913 / 1000000000000)
      | 2 => orderedInterval (2344029050 / 1000000000000) (2344029217 / 1000000000000)
      | 3 => orderedInterval (23205487073 / 1000000000000) (23205487459 / 1000000000000)
      | 4 => orderedInterval (5609940058 / 1000000000000) (5609940874 / 1000000000000)
      | 5 => orderedInterval (5454202308 / 1000000000000) (5454203054 / 1000000000000)
      | 6 => orderedInterval (8069055717 / 1000000000000) (8069059645 / 1000000000000)
      | 7 => orderedInterval (4312851228 / 1000000000000) (4312860953 / 1000000000000)
      | _ => orderedInterval (-2349507613 / 1000000000000) (-2349494942 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17288322133 / 1000000000000) (17288322157 / 1000000000000)
      | 1 => orderedInterval (9929647701 / 1000000000000) (9929647763 / 1000000000000)
      | 2 => orderedInterval (2290557804 / 1000000000000) (2290558063 / 1000000000000)
      | 3 => orderedInterval (8903569305 / 1000000000000) (8903570150 / 1000000000000)
      | 4 => orderedInterval (6374783294 / 1000000000000) (6374785008 / 1000000000000)
      | 5 => orderedInterval (4448115786 / 1000000000000) (4448116888 / 1000000000000)
      | 6 => orderedInterval (-2397662880 / 1000000000000) (-2397658875 / 1000000000000)
      | 7 => orderedInterval (-3710656606 / 1000000000000) (-3710646165 / 1000000000000)
      | _ => orderedInterval (27162065534 / 1000000000000) (27162081203 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1859936307 / 1000000000000) (-1859936280 / 1000000000000)
      | 1 => orderedInterval (-8862727817 / 1000000000000) (-8862727722 / 1000000000000)
      | 2 => orderedInterval (-13212910120 / 1000000000000) (-13212909711 / 1000000000000)
      | 3 => orderedInterval (-110245485148 / 1000000000000) (-110245483270 / 1000000000000)
      | 4 => orderedInterval (-6064993871 / 1000000000000) (-6064990244 / 1000000000000)
      | 5 => orderedInterval (-15584985269 / 1000000000000) (-15584983624 / 1000000000000)
      | 6 => orderedInterval (-8071677936 / 1000000000000) (-8071673829 / 1000000000000)
      | 7 => orderedInterval (-4589112154 / 1000000000000) (-4589100875 / 1000000000000)
      | _ => orderedInterval (-11212831738 / 1000000000000) (-11212812184 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-26399493937 / 1000000000000) (-26399472212 / 1000000000000)
    | 1 => orderedInterval (-39377912489 / 1000000000000) (-39377888033 / 1000000000000)
    | 2 => orderedInterval (53155926140 / 1000000000000) (53155954642 / 1000000000000)
    | 3 => orderedInterval (70288742071 / 1000000000000) (70288776192 / 1000000000000)
    | _ => orderedInterval (-179704660360 / 1000000000000) (-179704617739 / 1000000000000)

theorem compactCertificate344_stateChecks0 :
    compactCertificate344.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (865 / 4)) (orderedInterval (-14206775281 / 1000000000000) (-14206775280 / 1000000000000), orderedInterval (-52332033385 / 1000000000000) (-52332033384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (254862033986873 / 1600000000000)) (orderedInterval (9312302324 / 1000000000000) (9312302365 / 1000000000000), orderedInterval (-62558737380 / 1000000000000) (-62558737339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (82417145320409 / 320000000000)) (orderedInterval (33076746721 / 1000000000000) (33076746722 / 1000000000000), orderedInterval (37053502888 / 1000000000000) (37053502889 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks1 :
    compactCertificate344.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (74368105882411 / 1600000000000)) (orderedInterval (-16201493921 / 1000000000000) (-16201493919 / 1000000000000), orderedInterval (-115734719381 / 1000000000000) (-115734719379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (199763193139567 / 1600000000000)) (orderedInterval (-1950125938 / 1000000000000) (-1950125930 / 1000000000000), orderedInterval (71388713209 / 1000000000000) (71388713218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (542395928849139 / 1600000000000)) (orderedInterval (20412993427 / 1000000000000) (20412993428 / 1000000000000), orderedInterval (38196314491 / 1000000000000) (38196314492 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks2 :
    compactCertificate344.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (399526386279307 / 1600000000000)) (orderedInterval (-37549113569 / 1000000000000) (-37549053188 / 1000000000000), orderedInterval (33832577022 / 1000000000000) (33832637403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (684595272598711 / 1600000000000)) (orderedInterval (38015315539 / 1000000000000) (38015315570 / 1000000000000), orderedInterval (6490789763 / 1000000000000) (6490789793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (504269779283749 / 1600000000000)) (orderedInterval (43825275048 / 1000000000000) (43825277484 / 1000000000000), orderedInterval (-10033301709 / 1000000000000) (-10033299274 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks3 :
    compactCertificate344.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (773679520214827 / 1600000000000)) (orderedInterval (18329522591 / 1000000000000) (18329522592 / 1000000000000), orderedInterval (31295323861 / 1000000000000) (31295323862 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (446684079262483 / 1600000000000)) (orderedInterval (-16855788776 / 1000000000000) (-16855788775 / 1000000000000), orderedInterval (-44648948661 / 1000000000000) (-44648948660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (792648737208047 / 1600000000000)) (orderedInterval (-6454189795 / 1000000000000) (-6454189790 / 1000000000000), orderedInterval (35268277996 / 1000000000000) (35268278001 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks4 :
    compactCertificate344.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (740595269989643 / 1600000000000)) (orderedInterval (-35719966023 / 1000000000000) (-35719957040 / 1000000000000), orderedInterval (10011166082 / 1000000000000) (10011175064 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (528523730151419 / 1600000000000)) (orderedInterval (-41592702519 / 1000000000000) (-41592702517 / 1000000000000), orderedInterval (-13982843892 / 1000000000000) (-13982843891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (599289579418701 / 1600000000000)) (orderedInterval (-41097513960 / 1000000000000) (-41097513882 / 1000000000000), orderedInterval (-3209804208 / 1000000000000) (-3209804130 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks5 :
    compactCertificate344.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (499625172239869 / 1600000000000)) (orderedInterval (-40413198523 / 1000000000000) (-40413171639 / 1000000000000), orderedInterval (20201340413 / 1000000000000) (20201367298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (441433991785249 / 1600000000000)) (orderedInterval (10531458708 / 1000000000000) (10531458709 / 1000000000000), orderedInterval (46848308062 / 1000000000000) (46848308063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (127944776535651 / 320000000000)) (orderedInterval (-39832330483 / 1000000000000) (-39832329895 / 1000000000000), orderedInterval (2420593998 / 1000000000000) (2420594586 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks6 :
    compactCertificate344.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (353901985262297 / 1600000000000)) (orderedInterval (47303213530 / 1000000000000) (47303236483 / 1000000000000), orderedInterval (-25416526921 / 1000000000000) (-25416503967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (300006632264017 / 1600000000000)) (orderedInterval (-11957522278 / 1000000000000) (-11957522200 / 1000000000000), orderedInterval (57060467259 / 1000000000000) (57060467337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (187730220716251 / 1600000000000)) (orderedInterval (-70238177412 / 1000000000000) (-70238175403 / 1000000000000), orderedInterval (22489056629 / 1000000000000) (22489058637 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks7 :
    compactCertificate344.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (100961937063717 / 1600000000000)) (orderedInterval (87263886815 / 1000000000000) (87263886816 / 1000000000000), orderedInterval (49045094601 / 1000000000000) (49045094602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (274131299022151 / 1600000000000)) (orderedInterval (37894441041 / 1000000000000) (37894459906 / 1000000000000), orderedInterval (-47857023613 / 1000000000000) (-47857004749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (374302852609127 / 1600000000000)) (orderedInterval (40710236952 / 1000000000000) (40710341657 / 1000000000000), orderedInterval (-32705678733 / 1000000000000) (-32705574028 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_stateChecks8 :
    compactCertificate344.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (158269779283749 / 1600000000000)) (orderedInterval (-59102477433 / 1000000000000) (-59102372141 / 1000000000000), orderedInterval (54545242752 / 1000000000000) (54545348044 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (643357865913029 / 1600000000000)) (orderedInterval (27409099285 / 1000000000000) (27409099286 / 1000000000000), orderedInterval (28810050782 / 1000000000000) (28810050783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (429733238612011 / 1600000000000)) (orderedInterval (-35220741896 / 1000000000000) (-35220699172 / 1000000000000), orderedInterval (33677876791 / 1000000000000) (33677919515 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_states : ∀ j,
    BesselStateValid (compactCertificate344.point j) (compactCertificate344.state j) :=
  compactCertificate344.statesValid_of_checks3 compactCertificate344_stateChecks0
    compactCertificate344_stateChecks1 compactCertificate344_stateChecks2
    compactCertificate344_stateChecks3 compactCertificate344_stateChecks4
    compactCertificate344_stateChecks5 compactCertificate344_stateChecks6
    compactCertificate344_stateChecks7 compactCertificate344_stateChecks8

theorem compactCertificate344_chunkChecks0_0 :
    compactCertificate344.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (865 / 4) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14206775281 / 1000000000000) (-14206775280 / 1000000000000), orderedInterval (-52332033385 / 1000000000000) (-52332033384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (254862033986873 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9312302324 / 1000000000000) (9312302365 / 1000000000000), orderedInterval (-62558737380 / 1000000000000) (-62558737339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (82417145320409 / 320000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33076746721 / 1000000000000) (33076746722 / 1000000000000), orderedInterval (37053502888 / 1000000000000) (37053502889 / 1000000000000)))) (orderedInterval (-3603314596 / 1000000000000) (-3603314579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (74368105882411 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16201493921 / 1000000000000) (-16201493919 / 1000000000000), orderedInterval (-115734719381 / 1000000000000) (-115734719379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (199763193139567 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1950125938 / 1000000000000) (-1950125930 / 1000000000000), orderedInterval (71388713209 / 1000000000000) (71388713218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (542395928849139 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20412993427 / 1000000000000) (20412993428 / 1000000000000), orderedInterval (38196314491 / 1000000000000) (38196314492 / 1000000000000)))) (orderedInterval (-1346580169 / 1000000000000) (-1346580142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (399526386279307 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37549113569 / 1000000000000) (-37549053188 / 1000000000000), orderedInterval (33832577022 / 1000000000000) (33832637403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (684595272598711 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38015315539 / 1000000000000) (38015315570 / 1000000000000), orderedInterval (6490789763 / 1000000000000) (6490789793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (504269779283749 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (43825275048 / 1000000000000) (43825277484 / 1000000000000), orderedInterval (-10033301709 / 1000000000000) (-10033299274 / 1000000000000)))) (orderedInterval (-113374007 / 1000000000000) (-113373935 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks0_1 :
    compactCertificate344.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (773679520214827 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18329522591 / 1000000000000) (18329522592 / 1000000000000), orderedInterval (31295323861 / 1000000000000) (31295323862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (446684079262483 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16855788776 / 1000000000000) (-16855788775 / 1000000000000), orderedInterval (-44648948661 / 1000000000000) (-44648948660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (792648737208047 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6454189795 / 1000000000000) (-6454189790 / 1000000000000), orderedInterval (35268277996 / 1000000000000) (35268278001 / 1000000000000)))) (orderedInterval (-5423311246 / 1000000000000) (-5423311159 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (740595269989643 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35719966023 / 1000000000000) (-35719957040 / 1000000000000), orderedInterval (10011166082 / 1000000000000) (10011175064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (528523730151419 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41592702519 / 1000000000000) (-41592702517 / 1000000000000), orderedInterval (-13982843892 / 1000000000000) (-13982843891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (599289579418701 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41097513960 / 1000000000000) (-41097513882 / 1000000000000), orderedInterval (-3209804208 / 1000000000000) (-3209804130 / 1000000000000)))) (orderedInterval (-3080292619 / 1000000000000) (-3080292430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (499625172239869 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40413198523 / 1000000000000) (-40413171639 / 1000000000000), orderedInterval (20201340413 / 1000000000000) (20201367298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (441433991785249 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10531458708 / 1000000000000) (10531458709 / 1000000000000), orderedInterval (46848308062 / 1000000000000) (46848308063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (127944776535651 / 320000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-39832330483 / 1000000000000) (-39832329895 / 1000000000000), orderedInterval (2420593998 / 1000000000000) (2420594586 / 1000000000000)))) (orderedInterval (-2089223675 / 1000000000000) (-2089223328 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks0_2 :
    compactCertificate344.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (353901985262297 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47303213530 / 1000000000000) (47303236483 / 1000000000000), orderedInterval (-25416526921 / 1000000000000) (-25416503967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (300006632264017 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11957522278 / 1000000000000) (-11957522200 / 1000000000000), orderedInterval (57060467259 / 1000000000000) (57060467337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (187730220716251 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-70238177412 / 1000000000000) (-70238175403 / 1000000000000), orderedInterval (22489056629 / 1000000000000) (22489058637 / 1000000000000)))) (orderedInterval (-9173257693 / 1000000000000) (-9173253898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (100961937063717 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87263886815 / 1000000000000) (87263886816 / 1000000000000), orderedInterval (49045094601 / 1000000000000) (49045094602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (274131299022151 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37894441041 / 1000000000000) (37894459906 / 1000000000000), orderedInterval (-47857023613 / 1000000000000) (-47857004749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (374302852609127 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40710236952 / 1000000000000) (40710341657 / 1000000000000), orderedInterval (-32705678733 / 1000000000000) (-32705574028 / 1000000000000)))) (orderedInterval (-5591038858 / 1000000000000) (-5591030379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (158269779283749 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59102477433 / 1000000000000) (-59102372141 / 1000000000000), orderedInterval (54545242752 / 1000000000000) (54545348044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (643357865913029 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27409099285 / 1000000000000) (27409099286 / 1000000000000), orderedInterval (28810050782 / 1000000000000) (28810050783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (429733238612011 / 1600000000000) 0 (IntervalRat.scale (865 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35220741896 / 1000000000000) (-35220699172 / 1000000000000), orderedInterval (33677876791 / 1000000000000) (33677919515 / 1000000000000)))) (orderedInterval (4020898926 / 1000000000000) (4020907638 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks0 :
    compactCertificate344.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate344.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate344_chunkChecks0_0
    compactCertificate344_chunkChecks0_1 compactCertificate344_chunkChecks0_2

theorem compactCertificate344_chunkChecks1_0 :
    compactCertificate344.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (865 / 4) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14206775281 / 1000000000000) (-14206775280 / 1000000000000), orderedInterval (-52332033385 / 1000000000000) (-52332033384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (254862033986873 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9312302324 / 1000000000000) (9312302365 / 1000000000000), orderedInterval (-62558737380 / 1000000000000) (-62558737339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (82417145320409 / 320000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33076746721 / 1000000000000) (33076746722 / 1000000000000), orderedInterval (37053502888 / 1000000000000) (37053502889 / 1000000000000)))) (orderedInterval (-18582327404 / 1000000000000) (-18582327386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (74368105882411 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16201493921 / 1000000000000) (-16201493919 / 1000000000000), orderedInterval (-115734719381 / 1000000000000) (-115734719379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (199763193139567 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1950125938 / 1000000000000) (-1950125930 / 1000000000000), orderedInterval (71388713209 / 1000000000000) (71388713218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (542395928849139 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20412993427 / 1000000000000) (20412993428 / 1000000000000), orderedInterval (38196314491 / 1000000000000) (38196314492 / 1000000000000)))) (orderedInterval (-2481889717 / 1000000000000) (-2481889686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (399526386279307 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37549113569 / 1000000000000) (-37549053188 / 1000000000000), orderedInterval (33832577022 / 1000000000000) (33832637403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (684595272598711 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38015315539 / 1000000000000) (38015315570 / 1000000000000), orderedInterval (6490789763 / 1000000000000) (6490789793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (504269779283749 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (43825275048 / 1000000000000) (43825277484 / 1000000000000), orderedInterval (-10033301709 / 1000000000000) (-10033299274 / 1000000000000)))) (orderedInterval (-749523722 / 1000000000000) (-749523612 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks1_1 :
    compactCertificate344.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (773679520214827 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18329522591 / 1000000000000) (18329522592 / 1000000000000), orderedInterval (31295323861 / 1000000000000) (31295323862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (446684079262483 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16855788776 / 1000000000000) (-16855788775 / 1000000000000), orderedInterval (-44648948661 / 1000000000000) (-44648948660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (792648737208047 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6454189795 / 1000000000000) (-6454189790 / 1000000000000), orderedInterval (35268277996 / 1000000000000) (35268278001 / 1000000000000)))) (orderedInterval (-5219490897 / 1000000000000) (-5219490717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (740595269989643 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35719966023 / 1000000000000) (-35719957040 / 1000000000000), orderedInterval (10011166082 / 1000000000000) (10011175064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (528523730151419 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41592702519 / 1000000000000) (-41592702517 / 1000000000000), orderedInterval (-13982843892 / 1000000000000) (-13982843891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (599289579418701 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41097513960 / 1000000000000) (-41097513882 / 1000000000000), orderedInterval (-3209804208 / 1000000000000) (-3209804130 / 1000000000000)))) (orderedInterval (-2378496548 / 1000000000000) (-2378496157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (499625172239869 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40413198523 / 1000000000000) (-40413171639 / 1000000000000), orderedInterval (20201340413 / 1000000000000) (20201367298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (441433991785249 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10531458708 / 1000000000000) (10531458709 / 1000000000000), orderedInterval (46848308062 / 1000000000000) (46848308063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (127944776535651 / 320000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-39832330483 / 1000000000000) (-39832329895 / 1000000000000), orderedInterval (2420593998 / 1000000000000) (2420594586 / 1000000000000)))) (orderedInterval (-2968996619 / 1000000000000) (-2968996112 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks1_2 :
    compactCertificate344.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (353901985262297 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47303213530 / 1000000000000) (47303236483 / 1000000000000), orderedInterval (-25416526921 / 1000000000000) (-25416503967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (300006632264017 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11957522278 / 1000000000000) (-11957522200 / 1000000000000), orderedInterval (57060467259 / 1000000000000) (57060467337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (187730220716251 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-70238177412 / 1000000000000) (-70238175403 / 1000000000000), orderedInterval (22489056629 / 1000000000000) (22489058637 / 1000000000000)))) (orderedInterval (1753646264 / 1000000000000) (1753650108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (100961937063717 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87263886815 / 1000000000000) (87263886816 / 1000000000000), orderedInterval (49045094601 / 1000000000000) (49045094602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (274131299022151 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37894441041 / 1000000000000) (37894459906 / 1000000000000), orderedInterval (-47857023613 / 1000000000000) (-47857004749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (374302852609127 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40710236952 / 1000000000000) (40710341657 / 1000000000000), orderedInterval (-32705678733 / 1000000000000) (-32705574028 / 1000000000000)))) (orderedInterval (3307499146 / 1000000000000) (3307508190 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (158269779283749 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59102477433 / 1000000000000) (-59102372141 / 1000000000000), orderedInterval (54545242752 / 1000000000000) (54545348044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (643357865913029 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27409099285 / 1000000000000) (27409099286 / 1000000000000), orderedInterval (28810050782 / 1000000000000) (28810050783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (429733238612011 / 1600000000000) 1 (IntervalRat.scale (865 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35220741896 / 1000000000000) (-35220699172 / 1000000000000), orderedInterval (33677876791 / 1000000000000) (33677919515 / 1000000000000)))) (orderedInterval (-12058332992 / 1000000000000) (-12058322661 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks1 :
    compactCertificate344.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate344.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate344_chunkChecks1_0
    compactCertificate344_chunkChecks1_1 compactCertificate344_chunkChecks1_2

theorem compactCertificate344_chunkChecks2_0 :
    compactCertificate344.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (865 / 4) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14206775281 / 1000000000000) (-14206775280 / 1000000000000), orderedInterval (-52332033385 / 1000000000000) (-52332033384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (254862033986873 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9312302324 / 1000000000000) (9312302365 / 1000000000000), orderedInterval (-62558737380 / 1000000000000) (-62558737339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (82417145320409 / 320000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33076746721 / 1000000000000) (33076746722 / 1000000000000), orderedInterval (37053502888 / 1000000000000) (37053502889 / 1000000000000)))) (orderedInterval (2916676448 / 1000000000000) (2916676469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (74368105882411 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16201493921 / 1000000000000) (-16201493919 / 1000000000000), orderedInterval (-115734719381 / 1000000000000) (-115734719379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (199763193139567 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1950125938 / 1000000000000) (-1950125930 / 1000000000000), orderedInterval (71388713209 / 1000000000000) (71388713218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (542395928849139 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20412993427 / 1000000000000) (20412993428 / 1000000000000), orderedInterval (38196314491 / 1000000000000) (38196314492 / 1000000000000)))) (orderedInterval (3593191871 / 1000000000000) (3593191913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (399526386279307 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37549113569 / 1000000000000) (-37549053188 / 1000000000000), orderedInterval (33832577022 / 1000000000000) (33832637403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (684595272598711 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38015315539 / 1000000000000) (38015315570 / 1000000000000), orderedInterval (6490789763 / 1000000000000) (6490789793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (504269779283749 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (43825275048 / 1000000000000) (43825277484 / 1000000000000), orderedInterval (-10033301709 / 1000000000000) (-10033299274 / 1000000000000)))) (orderedInterval (2344029050 / 1000000000000) (2344029217 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks2_1 :
    compactCertificate344.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (773679520214827 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18329522591 / 1000000000000) (18329522592 / 1000000000000), orderedInterval (31295323861 / 1000000000000) (31295323862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (446684079262483 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16855788776 / 1000000000000) (-16855788775 / 1000000000000), orderedInterval (-44648948661 / 1000000000000) (-44648948660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (792648737208047 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6454189795 / 1000000000000) (-6454189790 / 1000000000000), orderedInterval (35268277996 / 1000000000000) (35268278001 / 1000000000000)))) (orderedInterval (23205487073 / 1000000000000) (23205487459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (740595269989643 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35719966023 / 1000000000000) (-35719957040 / 1000000000000), orderedInterval (10011166082 / 1000000000000) (10011175064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (528523730151419 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41592702519 / 1000000000000) (-41592702517 / 1000000000000), orderedInterval (-13982843892 / 1000000000000) (-13982843891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (599289579418701 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41097513960 / 1000000000000) (-41097513882 / 1000000000000), orderedInterval (-3209804208 / 1000000000000) (-3209804130 / 1000000000000)))) (orderedInterval (5609940058 / 1000000000000) (5609940874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (499625172239869 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40413198523 / 1000000000000) (-40413171639 / 1000000000000), orderedInterval (20201340413 / 1000000000000) (20201367298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (441433991785249 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10531458708 / 1000000000000) (10531458709 / 1000000000000), orderedInterval (46848308062 / 1000000000000) (46848308063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (127944776535651 / 320000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-39832330483 / 1000000000000) (-39832329895 / 1000000000000), orderedInterval (2420593998 / 1000000000000) (2420594586 / 1000000000000)))) (orderedInterval (5454202308 / 1000000000000) (5454203054 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks2_2 :
    compactCertificate344.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (353901985262297 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47303213530 / 1000000000000) (47303236483 / 1000000000000), orderedInterval (-25416526921 / 1000000000000) (-25416503967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (300006632264017 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11957522278 / 1000000000000) (-11957522200 / 1000000000000), orderedInterval (57060467259 / 1000000000000) (57060467337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (187730220716251 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-70238177412 / 1000000000000) (-70238175403 / 1000000000000), orderedInterval (22489056629 / 1000000000000) (22489058637 / 1000000000000)))) (orderedInterval (8069055717 / 1000000000000) (8069059645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (100961937063717 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87263886815 / 1000000000000) (87263886816 / 1000000000000), orderedInterval (49045094601 / 1000000000000) (49045094602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (274131299022151 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37894441041 / 1000000000000) (37894459906 / 1000000000000), orderedInterval (-47857023613 / 1000000000000) (-47857004749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (374302852609127 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40710236952 / 1000000000000) (40710341657 / 1000000000000), orderedInterval (-32705678733 / 1000000000000) (-32705574028 / 1000000000000)))) (orderedInterval (4312851228 / 1000000000000) (4312860953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (158269779283749 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59102477433 / 1000000000000) (-59102372141 / 1000000000000), orderedInterval (54545242752 / 1000000000000) (54545348044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (643357865913029 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27409099285 / 1000000000000) (27409099286 / 1000000000000), orderedInterval (28810050782 / 1000000000000) (28810050783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (429733238612011 / 1600000000000) 2 (IntervalRat.scale (865 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35220741896 / 1000000000000) (-35220699172 / 1000000000000), orderedInterval (33677876791 / 1000000000000) (33677919515 / 1000000000000)))) (orderedInterval (-2349507613 / 1000000000000) (-2349494942 / 1000000000000))) = true
  rfl'

theorem compactCertificate344_chunkChecks2 :
    compactCertificate344.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate344.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate344_chunkChecks2_0
    compactCertificate344_chunkChecks2_1 compactCertificate344_chunkChecks2_2

theorem compactCertificate344_chunkChecks3_0 :
    compactCertificate344.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (865 / 4) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14206775281 / 1000000000000) (-14206775280 / 1000000000000), orderedInterval (-52332033385 / 1000000000000) (-52332033384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (254862033986873 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9312302324 / 1000000000000) (9312302365 / 1000000000000), orderedInterval (-62558737380 / 1000000000000) (-62558737339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (82417145320409 / 320000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33076746721 / 1000000000000) (33076746722 / 1000000000000), orderedInterval (37053502888 / 1000000000000) (37053502889 / 1000000000000)))) (orderedInterval (17288322133 / 1000000000000) (17288322157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (74368105882411 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16201493921 / 1000000000000) (-16201493919 / 1000000000000), orderedInterval (-115734719381 / 1000000000000) (-115734719379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (199763193139567 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1950125938 / 1000000000000) (-1950125930 / 1000000000000), orderedInterval (71388713209 / 1000000000000) (71388713218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (542395928849139 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20412993427 / 1000000000000) (20412993428 / 1000000000000), orderedInterval (38196314491 / 1000000000000) (38196314492 / 1000000000000)))) (orderedInterval (9929647701 / 1000000000000) (9929647763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (399526386279307 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37549113569 / 1000000000000) (-37549053188 / 1000000000000), orderedInterval (33832577022 / 1000000000000) (33832637403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (684595272598711 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38015315539 / 1000000000000) (38015315570 / 1000000000000), orderedInterval (6490789763 / 1000000000000) (6490789793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (504269779283749 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (43825275048 / 1000000000000) (43825277484 / 1000000000000), orderedInterval (-10033301709 / 1000000000000) (-10033299274 / 1000000000000)))) (orderedInterval (2290557804 / 1000000000000) (2290558063 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate344_chunkChecks3_1 :
    compactCertificate344.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (773679520214827 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18329522591 / 1000000000000) (18329522592 / 1000000000000), orderedInterval (31295323861 / 1000000000000) (31295323862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (446684079262483 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16855788776 / 1000000000000) (-16855788775 / 1000000000000), orderedInterval (-44648948661 / 1000000000000) (-44648948660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (792648737208047 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6454189795 / 1000000000000) (-6454189790 / 1000000000000), orderedInterval (35268277996 / 1000000000000) (35268278001 / 1000000000000)))) (orderedInterval (8903569305 / 1000000000000) (8903570150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (740595269989643 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35719966023 / 1000000000000) (-35719957040 / 1000000000000), orderedInterval (10011166082 / 1000000000000) (10011175064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (528523730151419 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41592702519 / 1000000000000) (-41592702517 / 1000000000000), orderedInterval (-13982843892 / 1000000000000) (-13982843891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (599289579418701 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41097513960 / 1000000000000) (-41097513882 / 1000000000000), orderedInterval (-3209804208 / 1000000000000) (-3209804130 / 1000000000000)))) (orderedInterval (6374783294 / 1000000000000) (6374785008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (499625172239869 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40413198523 / 1000000000000) (-40413171639 / 1000000000000), orderedInterval (20201340413 / 1000000000000) (20201367298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (441433991785249 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10531458708 / 1000000000000) (10531458709 / 1000000000000), orderedInterval (46848308062 / 1000000000000) (46848308063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (127944776535651 / 320000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-39832330483 / 1000000000000) (-39832329895 / 1000000000000), orderedInterval (2420593998 / 1000000000000) (2420594586 / 1000000000000)))) (orderedInterval (4448115786 / 1000000000000) (4448116888 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate344_chunkChecks3_2 :
    compactCertificate344.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (353901985262297 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47303213530 / 1000000000000) (47303236483 / 1000000000000), orderedInterval (-25416526921 / 1000000000000) (-25416503967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (300006632264017 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11957522278 / 1000000000000) (-11957522200 / 1000000000000), orderedInterval (57060467259 / 1000000000000) (57060467337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (187730220716251 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-70238177412 / 1000000000000) (-70238175403 / 1000000000000), orderedInterval (22489056629 / 1000000000000) (22489058637 / 1000000000000)))) (orderedInterval (-2397662880 / 1000000000000) (-2397658875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (100961937063717 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87263886815 / 1000000000000) (87263886816 / 1000000000000), orderedInterval (49045094601 / 1000000000000) (49045094602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (274131299022151 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37894441041 / 1000000000000) (37894459906 / 1000000000000), orderedInterval (-47857023613 / 1000000000000) (-47857004749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (374302852609127 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40710236952 / 1000000000000) (40710341657 / 1000000000000), orderedInterval (-32705678733 / 1000000000000) (-32705574028 / 1000000000000)))) (orderedInterval (-3710656606 / 1000000000000) (-3710646165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (158269779283749 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59102477433 / 1000000000000) (-59102372141 / 1000000000000), orderedInterval (54545242752 / 1000000000000) (54545348044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (643357865913029 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27409099285 / 1000000000000) (27409099286 / 1000000000000), orderedInterval (28810050782 / 1000000000000) (28810050783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (429733238612011 / 1600000000000) 3 (IntervalRat.scale (865 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35220741896 / 1000000000000) (-35220699172 / 1000000000000), orderedInterval (33677876791 / 1000000000000) (33677919515 / 1000000000000)))) (orderedInterval (27162065534 / 1000000000000) (27162081203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate344_chunkChecks3 :
    compactCertificate344.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate344.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate344_chunkChecks3_0
    compactCertificate344_chunkChecks3_1 compactCertificate344_chunkChecks3_2

theorem compactCertificate344_chunkChecks4_0 :
    compactCertificate344.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (865 / 4) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14206775281 / 1000000000000) (-14206775280 / 1000000000000), orderedInterval (-52332033385 / 1000000000000) (-52332033384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (254862033986873 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9312302324 / 1000000000000) (9312302365 / 1000000000000), orderedInterval (-62558737380 / 1000000000000) (-62558737339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (82417145320409 / 320000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33076746721 / 1000000000000) (33076746722 / 1000000000000), orderedInterval (37053502888 / 1000000000000) (37053502889 / 1000000000000)))) (orderedInterval (-1859936307 / 1000000000000) (-1859936280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (74368105882411 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16201493921 / 1000000000000) (-16201493919 / 1000000000000), orderedInterval (-115734719381 / 1000000000000) (-115734719379 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (199763193139567 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1950125938 / 1000000000000) (-1950125930 / 1000000000000), orderedInterval (71388713209 / 1000000000000) (71388713218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (542395928849139 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20412993427 / 1000000000000) (20412993428 / 1000000000000), orderedInterval (38196314491 / 1000000000000) (38196314492 / 1000000000000)))) (orderedInterval (-8862727817 / 1000000000000) (-8862727722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (399526386279307 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-37549113569 / 1000000000000) (-37549053188 / 1000000000000), orderedInterval (33832577022 / 1000000000000) (33832637403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (684595272598711 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38015315539 / 1000000000000) (38015315570 / 1000000000000), orderedInterval (6490789763 / 1000000000000) (6490789793 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (504269779283749 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (43825275048 / 1000000000000) (43825277484 / 1000000000000), orderedInterval (-10033301709 / 1000000000000) (-10033299274 / 1000000000000)))) (orderedInterval (-13212910120 / 1000000000000) (-13212909711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate344_chunkChecks4_1 :
    compactCertificate344.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (773679520214827 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18329522591 / 1000000000000) (18329522592 / 1000000000000), orderedInterval (31295323861 / 1000000000000) (31295323862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (446684079262483 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16855788776 / 1000000000000) (-16855788775 / 1000000000000), orderedInterval (-44648948661 / 1000000000000) (-44648948660 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (792648737208047 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6454189795 / 1000000000000) (-6454189790 / 1000000000000), orderedInterval (35268277996 / 1000000000000) (35268278001 / 1000000000000)))) (orderedInterval (-110245485148 / 1000000000000) (-110245483270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (740595269989643 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-35719966023 / 1000000000000) (-35719957040 / 1000000000000), orderedInterval (10011166082 / 1000000000000) (10011175064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (528523730151419 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41592702519 / 1000000000000) (-41592702517 / 1000000000000), orderedInterval (-13982843892 / 1000000000000) (-13982843891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (599289579418701 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41097513960 / 1000000000000) (-41097513882 / 1000000000000), orderedInterval (-3209804208 / 1000000000000) (-3209804130 / 1000000000000)))) (orderedInterval (-6064993871 / 1000000000000) (-6064990244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (499625172239869 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40413198523 / 1000000000000) (-40413171639 / 1000000000000), orderedInterval (20201340413 / 1000000000000) (20201367298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (441433991785249 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (10531458708 / 1000000000000) (10531458709 / 1000000000000), orderedInterval (46848308062 / 1000000000000) (46848308063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (127944776535651 / 320000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-39832330483 / 1000000000000) (-39832329895 / 1000000000000), orderedInterval (2420593998 / 1000000000000) (2420594586 / 1000000000000)))) (orderedInterval (-15584985269 / 1000000000000) (-15584983624 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate344_chunkChecks4_2 :
    compactCertificate344.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (353901985262297 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (47303213530 / 1000000000000) (47303236483 / 1000000000000), orderedInterval (-25416526921 / 1000000000000) (-25416503967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (300006632264017 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11957522278 / 1000000000000) (-11957522200 / 1000000000000), orderedInterval (57060467259 / 1000000000000) (57060467337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (187730220716251 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-70238177412 / 1000000000000) (-70238175403 / 1000000000000), orderedInterval (22489056629 / 1000000000000) (22489058637 / 1000000000000)))) (orderedInterval (-8071677936 / 1000000000000) (-8071673829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (100961937063717 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (87263886815 / 1000000000000) (87263886816 / 1000000000000), orderedInterval (49045094601 / 1000000000000) (49045094602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (274131299022151 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (37894441041 / 1000000000000) (37894459906 / 1000000000000), orderedInterval (-47857023613 / 1000000000000) (-47857004749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (374302852609127 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40710236952 / 1000000000000) (40710341657 / 1000000000000), orderedInterval (-32705678733 / 1000000000000) (-32705574028 / 1000000000000)))) (orderedInterval (-4589112154 / 1000000000000) (-4589100875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (158269779283749 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59102477433 / 1000000000000) (-59102372141 / 1000000000000), orderedInterval (54545242752 / 1000000000000) (54545348044 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (643357865913029 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27409099285 / 1000000000000) (27409099286 / 1000000000000), orderedInterval (28810050782 / 1000000000000) (28810050783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (429733238612011 / 1600000000000) 4 (IntervalRat.scale (865 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35220741896 / 1000000000000) (-35220699172 / 1000000000000), orderedInterval (33677876791 / 1000000000000) (33677919515 / 1000000000000)))) (orderedInterval (-11212831738 / 1000000000000) (-11212812184 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate344_chunkChecks4 :
    compactCertificate344.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate344.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate344_chunkChecks4_0
    compactCertificate344_chunkChecks4_1 compactCertificate344_chunkChecks4_2

theorem compactCertificate344_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate344.chunkCheck r b = true :=
  compactCertificate344.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate344_chunkChecks0
    · exact compactCertificate344_chunkChecks1
    · exact compactCertificate344_chunkChecks2
    · exact compactCertificate344_chunkChecks3
    · exact compactCertificate344_chunkChecks4)

theorem compactCertificate344_coefficient0 :
    compactCertificate344.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate344_coefficient1 :
    compactCertificate344.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate344_coefficient2 :
    compactCertificate344.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate344_coefficient3 :
    compactCertificate344.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate344_coefficient4 :
    compactCertificate344.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate344_coefficients : ∀ r : Fin 5,
    compactCertificate344.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate344_coefficient0
  · exact compactCertificate344_coefficient1
  · exact compactCertificate344_coefficient2
  · exact compactCertificate344_coefficient3
  · exact compactCertificate344_coefficient4

theorem compactCertificate344_lower : (1 : ℚ) ≤ compactCertificate344.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate344, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate344_proves {t : ℝ} (ht : t ∈ compactCertificate344.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate344.proves compactCertificate344_states compactCertificate344_chunks
    compactCertificate344_coefficients compactCertificate344_lower ht

end Erdos232
