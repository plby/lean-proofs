/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate478 : CompactCertificate where
  left := 349
  right := 350
  center := 699 / 2
  grid := fun i =>
    match i.val with
    | 0 => 111
    | 1 => 82
    | 2 => 133
    | 3 => 24
    | 4 => 64
    | 5 => 174
    | 6 => 129
    | 7 => 220
    | 8 => 162
    | 9 => 249
    | 10 => 144
    | 11 => 255
    | 12 => 238
    | 13 => 170
    | 14 => 193
    | 15 => 161
    | 16 => 142
    | 17 => 206
    | 18 => 114
    | 19 => 97
    | 20 => 60
    | 21 => 32
    | 22 => 88
    | 23 => 120
    | 24 => 51
    | 25 => 207
    | _ => 138
  point := fun i =>
    match i.val with
    | 0 => 699 / 2
    | 1 => 1029760472582799 / 4000000000000
    | 2 => 333003379069167 / 800000000000
    | 3 => 300481537640493 / 4000000000000
    | 4 => 807135676326921 / 4000000000000
    | 5 => 2191530371477157 / 4000000000000
    | 6 => 1614271352654541 / 4000000000000
    | 7 => 2766081477147393 / 4000000000000
    | 8 => 2037483096643587 / 4000000000000
    | 9 => 3126023032544301 / 4000000000000
    | 10 => 1804810239332229 / 4000000000000
    | 11 => 3202667441089161 / 4000000000000
    | 12 => 2992347362559309 / 4000000000000
    | 13 => 2135480273848797 / 4000000000000
    | 14 => 2421407028980763 / 4000000000000
    | 15 => 2018716736391147 / 4000000000000
    | 16 => 1783597458138087 / 4000000000000
    | 17 => 516956062418613 / 800000000000
    | 18 => 1429927674556911 / 4000000000000
    | 19 => 1212165525737271 / 4000000000000
    | 20 => 758516903356413 / 4000000000000
    | 21 => 407932913338371 / 4000000000000
    | 22 => 1107617213968113 / 4000000000000
    | 23 => 1512356612565201 / 4000000000000
    | 24 => 639483096643587 / 4000000000000
    | 25 => 2599463284816227 / 4000000000000
    | _ => 1736321004565293 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-42679060318 / 1000000000000) (-42679060128 / 1000000000000), orderedInterval (-47363610 / 1000000000000) (-47363420 / 1000000000000))
    | 1 => (orderedInterval (28668002130 / 1000000000000) (28668002131 / 1000000000000), orderedInterval (40577215361 / 1000000000000) (40577215362 / 1000000000000))
    | 2 => (orderedInterval (27848925451 / 1000000000000) (27848943931 / 1000000000000), orderedInterval (-27489574100 / 1000000000000) (-27489555620 / 1000000000000))
    | 3 => (orderedInterval (44609905988 / 1000000000000) (44609905989 / 1000000000000), orderedInterval (80230828180 / 1000000000000) (80230828181 / 1000000000000))
    | 4 => (orderedInterval (56053829145 / 1000000000000) (56053829172 / 1000000000000), orderedInterval (3455064589 / 1000000000000) (3455064616 / 1000000000000))
    | 5 => (orderedInterval (30546573514 / 1000000000000) (30546649432 / 1000000000000), orderedInterval (-15156299071 / 1000000000000) (-15156223153 / 1000000000000))
    | 6 => (orderedInterval (31418532105 / 1000000000000) (31418590499 / 1000000000000), orderedInterval (-24336127148 / 1000000000000) (-24336068755 / 1000000000000))
    | 7 => (orderedInterval (27758767290 / 1000000000000) (27758767295 / 1000000000000), orderedInterval (12229807830 / 1000000000000) (12229807836 / 1000000000000))
    | 8 => (orderedInterval (33174347667 / 1000000000000) (33174347671 / 1000000000000), orderedInterval (12185384057 / 1000000000000) (12185384061 / 1000000000000))
    | 9 => (orderedInterval (-982357944 / 1000000000000) (-982357943 / 1000000000000), orderedInterval (-28523778060 / 1000000000000) (-28523778059 / 1000000000000))
    | 10 => (orderedInterval (-14684966556 / 1000000000000) (-14684966373 / 1000000000000), orderedInterval (34589274541 / 1000000000000) (34589274725 / 1000000000000))
    | 11 => (orderedInterval (-9562262882 / 1000000000000) (-9562262881 / 1000000000000), orderedInterval (-26520905083 / 1000000000000) (-26520905082 / 1000000000000))
    | 12 => (orderedInterval (26894251591 / 1000000000000) (26894251602 / 1000000000000), orderedInterval (11282301286 / 1000000000000) (11282301297 / 1000000000000))
    | 13 => (orderedInterval (19053635104 / 1000000000000) (19053635105 / 1000000000000), orderedInterval (28781828784 / 1000000000000) (28781828785 / 1000000000000))
    | 14 => (orderedInterval (6138336490 / 1000000000000) (6138336492 / 1000000000000), orderedInterval (-31848025258 / 1000000000000) (-31848025256 / 1000000000000))
    | 15 => (orderedInterval (11578882324 / 1000000000000) (11578882371 / 1000000000000), orderedInterval (-33587721279 / 1000000000000) (-33587721232 / 1000000000000))
    | 16 => (orderedInterval (20654231948 / 1000000000000) (20654231949 / 1000000000000), orderedInterval (31617380404 / 1000000000000) (31617380405 / 1000000000000))
    | 17 => (orderedInterval (-5860123998 / 1000000000000) (-5860123996 / 1000000000000), orderedInterval (30840248057 / 1000000000000) (30840248059 / 1000000000000))
    | 18 => (orderedInterval (5278219692 / 1000000000000) (5278219693 / 1000000000000), orderedInterval (41861302263 / 1000000000000) (41861302264 / 1000000000000))
    | 19 => (orderedInterval (36133214363 / 1000000000000) (36133301351 / 1000000000000), orderedInterval (-28258158315 / 1000000000000) (-28258071327 / 1000000000000))
    | 20 => (orderedInterval (54475620428 / 1000000000000) (54475625127 / 1000000000000), orderedInterval (-19881401274 / 1000000000000) (-19881396575 / 1000000000000))
    | 21 => (orderedInterval (62141778535 / 1000000000000) (62141842816 / 1000000000000), orderedInterval (-49097866612 / 1000000000000) (-49097802331 / 1000000000000))
    | 22 => (orderedInterval (45176412041 / 1000000000000) (45176412043 / 1000000000000), orderedInterval (15985457127 / 1000000000000) (15985457128 / 1000000000000))
    | 23 => (orderedInterval (39048983964 / 1000000000000) (39048992689 / 1000000000000), orderedInterval (-12659477732 / 1000000000000) (-12659469007 / 1000000000000))
    | 24 => (orderedInterval (-26544746819 / 1000000000000) (-26544746818 / 1000000000000), orderedInterval (-57166250038 / 1000000000000) (-57166250037 / 1000000000000))
    | 25 => (orderedInterval (-10477514963 / 1000000000000) (-10477514962 / 1000000000000), orderedInterval (-29484974518 / 1000000000000) (-29484974517 / 1000000000000))
    | _ => (orderedInterval (37150450921 / 1000000000000) (37150450931 / 1000000000000), orderedInterval (9254400171 / 1000000000000) (9254400181 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15015148599 / 1000000000000) (-15015147415 / 1000000000000)
      | 1 => orderedInterval (-608913043 / 1000000000000) (-608907602 / 1000000000000)
      | 2 => orderedInterval (-54432926 / 1000000000000) (-54432906 / 1000000000000)
      | 3 => orderedInterval (-2272814113 / 1000000000000) (-2272813960 / 1000000000000)
      | 4 => orderedInterval (1285178567 / 1000000000000) (1285178609 / 1000000000000)
      | 5 => orderedInterval (-1198306287 / 1000000000000) (-1198306253 / 1000000000000)
      | 6 => orderedInterval (-1115622161 / 1000000000000) (-1115616996 / 1000000000000)
      | 7 => orderedInterval (-5165038119 / 1000000000000) (-5165036221 / 1000000000000)
      | _ => orderedInterval (-6277542237 / 1000000000000) (-6277542138 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1661489964 / 1000000000000) (-1661488569 / 1000000000000)
      | 1 => orderedInterval (1574772866 / 1000000000000) (1574781375 / 1000000000000)
      | 2 => orderedInterval (-317152183 / 1000000000000) (-317152148 / 1000000000000)
      | 3 => orderedInterval (6004768203 / 1000000000000) (6004768509 / 1000000000000)
      | 4 => orderedInterval (4000639645 / 1000000000000) (4000639714 / 1000000000000)
      | 5 => orderedInterval (-1408525972 / 1000000000000) (-1408525922 / 1000000000000)
      | 6 => orderedInterval (-5810547080 / 1000000000000) (-5810542647 / 1000000000000)
      | 7 => orderedInterval (1026782450 / 1000000000000) (1026783557 / 1000000000000)
      | _ => orderedInterval (2148622237 / 1000000000000) (2148622376 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14458212062 / 1000000000000) (14458213711 / 1000000000000)
      | 1 => orderedInterval (4672058922 / 1000000000000) (4672072276 / 1000000000000)
      | 2 => orderedInterval (1649761804 / 1000000000000) (1649761866 / 1000000000000)
      | 3 => orderedInterval (8057474208 / 1000000000000) (8057474848 / 1000000000000)
      | 4 => orderedInterval (-1897938290 / 1000000000000) (-1897938177 / 1000000000000)
      | 5 => orderedInterval (2162063258 / 1000000000000) (2162063332 / 1000000000000)
      | 6 => orderedInterval (1915038475 / 1000000000000) (1915042312 / 1000000000000)
      | 7 => orderedInterval (4240415360 / 1000000000000) (4240416285 / 1000000000000)
      | _ => orderedInterval (7830901190 / 1000000000000) (7830901394 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (2551495160 / 1000000000000) (2551497109 / 1000000000000)
      | 1 => orderedInterval (-4179680985 / 1000000000000) (-4179660057 / 1000000000000)
      | 2 => orderedInterval (2005489233 / 1000000000000) (2005489346 / 1000000000000)
      | 3 => orderedInterval (-16874824796 / 1000000000000) (-16874823414 / 1000000000000)
      | 4 => orderedInterval (-8535328764 / 1000000000000) (-8535328572 / 1000000000000)
      | 5 => orderedInterval (-71762752 / 1000000000000) (-71762638 / 1000000000000)
      | 6 => orderedInterval (6217684993 / 1000000000000) (6217688314 / 1000000000000)
      | 7 => orderedInterval (-1082590670 / 1000000000000) (-1082589752 / 1000000000000)
      | _ => orderedInterval (-12092662798 / 1000000000000) (-12092662484 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13564169181 / 1000000000000) (-13564166869 / 1000000000000)
      | 1 => orderedInterval (-12863553861 / 1000000000000) (-12863520998 / 1000000000000)
      | 2 => orderedInterval (-9516170962 / 1000000000000) (-9516170755 / 1000000000000)
      | 3 => orderedInterval (-36002585350 / 1000000000000) (-36002582310 / 1000000000000)
      | 4 => orderedInterval (-612443326 / 1000000000000) (-612442991 / 1000000000000)
      | 5 => orderedInterval (-4303221216 / 1000000000000) (-4303221037 / 1000000000000)
      | 6 => orderedInterval (-1961556599 / 1000000000000) (-1961553710 / 1000000000000)
      | 7 => orderedInterval (-4504644488 / 1000000000000) (-4504643518 / 1000000000000)
      | _ => orderedInterval (-6328791583 / 1000000000000) (-6328791080 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-30422638918 / 1000000000000) (-30422624882 / 1000000000000)
    | 1 => orderedInterval (5557870202 / 1000000000000) (5557886245 / 1000000000000)
    | 2 => orderedInterval (43087986989 / 1000000000000) (43088007847 / 1000000000000)
    | 3 => orderedInterval (-32062181379 / 1000000000000) (-32062152148 / 1000000000000)
    | _ => orderedInterval (-89657136566 / 1000000000000) (-89657093268 / 1000000000000)

theorem compactCertificate478_stateChecks0 :
    compactCertificate478.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (699 / 2)) (orderedInterval (-42679060318 / 1000000000000) (-42679060128 / 1000000000000), orderedInterval (-47363610 / 1000000000000) (-47363420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1029760472582799 / 4000000000000)) (orderedInterval (28668002130 / 1000000000000) (28668002131 / 1000000000000), orderedInterval (40577215361 / 1000000000000) (40577215362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (333003379069167 / 800000000000)) (orderedInterval (27848925451 / 1000000000000) (27848943931 / 1000000000000), orderedInterval (-27489574100 / 1000000000000) (-27489555620 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks1 :
    compactCertificate478.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (300481537640493 / 4000000000000)) (orderedInterval (44609905988 / 1000000000000) (44609905989 / 1000000000000), orderedInterval (80230828180 / 1000000000000) (80230828181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (807135676326921 / 4000000000000)) (orderedInterval (56053829145 / 1000000000000) (56053829172 / 1000000000000), orderedInterval (3455064589 / 1000000000000) (3455064616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2191530371477157 / 4000000000000)) (orderedInterval (30546573514 / 1000000000000) (30546649432 / 1000000000000), orderedInterval (-15156299071 / 1000000000000) (-15156223153 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks2 :
    compactCertificate478.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1614271352654541 / 4000000000000)) (orderedInterval (31418532105 / 1000000000000) (31418590499 / 1000000000000), orderedInterval (-24336127148 / 1000000000000) (-24336068755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2766081477147393 / 4000000000000)) (orderedInterval (27758767290 / 1000000000000) (27758767295 / 1000000000000), orderedInterval (12229807830 / 1000000000000) (12229807836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2037483096643587 / 4000000000000)) (orderedInterval (33174347667 / 1000000000000) (33174347671 / 1000000000000), orderedInterval (12185384057 / 1000000000000) (12185384061 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks3 :
    compactCertificate478.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3126023032544301 / 4000000000000)) (orderedInterval (-982357944 / 1000000000000) (-982357943 / 1000000000000), orderedInterval (-28523778060 / 1000000000000) (-28523778059 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1804810239332229 / 4000000000000)) (orderedInterval (-14684966556 / 1000000000000) (-14684966373 / 1000000000000), orderedInterval (34589274541 / 1000000000000) (34589274725 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (3202667441089161 / 4000000000000)) (orderedInterval (-9562262882 / 1000000000000) (-9562262881 / 1000000000000), orderedInterval (-26520905083 / 1000000000000) (-26520905082 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks4 :
    compactCertificate478.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2992347362559309 / 4000000000000)) (orderedInterval (26894251591 / 1000000000000) (26894251602 / 1000000000000), orderedInterval (11282301286 / 1000000000000) (11282301297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2135480273848797 / 4000000000000)) (orderedInterval (19053635104 / 1000000000000) (19053635105 / 1000000000000), orderedInterval (28781828784 / 1000000000000) (28781828785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2421407028980763 / 4000000000000)) (orderedInterval (6138336490 / 1000000000000) (6138336492 / 1000000000000), orderedInterval (-31848025258 / 1000000000000) (-31848025256 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks5 :
    compactCertificate478.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2018716736391147 / 4000000000000)) (orderedInterval (11578882324 / 1000000000000) (11578882371 / 1000000000000), orderedInterval (-33587721279 / 1000000000000) (-33587721232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1783597458138087 / 4000000000000)) (orderedInterval (20654231948 / 1000000000000) (20654231949 / 1000000000000), orderedInterval (31617380404 / 1000000000000) (31617380405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (516956062418613 / 800000000000)) (orderedInterval (-5860123998 / 1000000000000) (-5860123996 / 1000000000000), orderedInterval (30840248057 / 1000000000000) (30840248059 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks6 :
    compactCertificate478.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1429927674556911 / 4000000000000)) (orderedInterval (5278219692 / 1000000000000) (5278219693 / 1000000000000), orderedInterval (41861302263 / 1000000000000) (41861302264 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1212165525737271 / 4000000000000)) (orderedInterval (36133214363 / 1000000000000) (36133301351 / 1000000000000), orderedInterval (-28258158315 / 1000000000000) (-28258071327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (758516903356413 / 4000000000000)) (orderedInterval (54475620428 / 1000000000000) (54475625127 / 1000000000000), orderedInterval (-19881401274 / 1000000000000) (-19881396575 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks7 :
    compactCertificate478.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (407932913338371 / 4000000000000)) (orderedInterval (62141778535 / 1000000000000) (62141842816 / 1000000000000), orderedInterval (-49097866612 / 1000000000000) (-49097802331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1107617213968113 / 4000000000000)) (orderedInterval (45176412041 / 1000000000000) (45176412043 / 1000000000000), orderedInterval (15985457127 / 1000000000000) (15985457128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1512356612565201 / 4000000000000)) (orderedInterval (39048983964 / 1000000000000) (39048992689 / 1000000000000), orderedInterval (-12659477732 / 1000000000000) (-12659469007 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_stateChecks8 :
    compactCertificate478.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (639483096643587 / 4000000000000)) (orderedInterval (-26544746819 / 1000000000000) (-26544746818 / 1000000000000), orderedInterval (-57166250038 / 1000000000000) (-57166250037 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2599463284816227 / 4000000000000)) (orderedInterval (-10477514963 / 1000000000000) (-10477514962 / 1000000000000), orderedInterval (-29484974518 / 1000000000000) (-29484974517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1736321004565293 / 4000000000000)) (orderedInterval (37150450921 / 1000000000000) (37150450931 / 1000000000000), orderedInterval (9254400171 / 1000000000000) (9254400181 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_states : ∀ j,
    BesselStateValid (compactCertificate478.point j) (compactCertificate478.state j) :=
  compactCertificate478.statesValid_of_checks3 compactCertificate478_stateChecks0
    compactCertificate478_stateChecks1 compactCertificate478_stateChecks2
    compactCertificate478_stateChecks3 compactCertificate478_stateChecks4
    compactCertificate478_stateChecks5 compactCertificate478_stateChecks6
    compactCertificate478_stateChecks7 compactCertificate478_stateChecks8

theorem compactCertificate478_chunkChecks0_0 :
    compactCertificate478.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (699 / 2) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42679060318 / 1000000000000) (-42679060128 / 1000000000000), orderedInterval (-47363610 / 1000000000000) (-47363420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1029760472582799 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28668002130 / 1000000000000) (28668002131 / 1000000000000), orderedInterval (40577215361 / 1000000000000) (40577215362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (333003379069167 / 800000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27848925451 / 1000000000000) (27848943931 / 1000000000000), orderedInterval (-27489574100 / 1000000000000) (-27489555620 / 1000000000000)))) (orderedInterval (-15015148599 / 1000000000000) (-15015147415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (300481537640493 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44609905988 / 1000000000000) (44609905989 / 1000000000000), orderedInterval (80230828180 / 1000000000000) (80230828181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (807135676326921 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56053829145 / 1000000000000) (56053829172 / 1000000000000), orderedInterval (3455064589 / 1000000000000) (3455064616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2191530371477157 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30546573514 / 1000000000000) (30546649432 / 1000000000000), orderedInterval (-15156299071 / 1000000000000) (-15156223153 / 1000000000000)))) (orderedInterval (-608913043 / 1000000000000) (-608907602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1614271352654541 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31418532105 / 1000000000000) (31418590499 / 1000000000000), orderedInterval (-24336127148 / 1000000000000) (-24336068755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2766081477147393 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27758767290 / 1000000000000) (27758767295 / 1000000000000), orderedInterval (12229807830 / 1000000000000) (12229807836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2037483096643587 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33174347667 / 1000000000000) (33174347671 / 1000000000000), orderedInterval (12185384057 / 1000000000000) (12185384061 / 1000000000000)))) (orderedInterval (-54432926 / 1000000000000) (-54432906 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks0_1 :
    compactCertificate478.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3126023032544301 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-982357944 / 1000000000000) (-982357943 / 1000000000000), orderedInterval (-28523778060 / 1000000000000) (-28523778059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1804810239332229 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14684966556 / 1000000000000) (-14684966373 / 1000000000000), orderedInterval (34589274541 / 1000000000000) (34589274725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3202667441089161 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9562262882 / 1000000000000) (-9562262881 / 1000000000000), orderedInterval (-26520905083 / 1000000000000) (-26520905082 / 1000000000000)))) (orderedInterval (-2272814113 / 1000000000000) (-2272813960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2992347362559309 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26894251591 / 1000000000000) (26894251602 / 1000000000000), orderedInterval (11282301286 / 1000000000000) (11282301297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2135480273848797 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19053635104 / 1000000000000) (19053635105 / 1000000000000), orderedInterval (28781828784 / 1000000000000) (28781828785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2421407028980763 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6138336490 / 1000000000000) (6138336492 / 1000000000000), orderedInterval (-31848025258 / 1000000000000) (-31848025256 / 1000000000000)))) (orderedInterval (1285178567 / 1000000000000) (1285178609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2018716736391147 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11578882324 / 1000000000000) (11578882371 / 1000000000000), orderedInterval (-33587721279 / 1000000000000) (-33587721232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1783597458138087 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20654231948 / 1000000000000) (20654231949 / 1000000000000), orderedInterval (31617380404 / 1000000000000) (31617380405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (516956062418613 / 800000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5860123998 / 1000000000000) (-5860123996 / 1000000000000), orderedInterval (30840248057 / 1000000000000) (30840248059 / 1000000000000)))) (orderedInterval (-1198306287 / 1000000000000) (-1198306253 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks0_2 :
    compactCertificate478.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1429927674556911 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5278219692 / 1000000000000) (5278219693 / 1000000000000), orderedInterval (41861302263 / 1000000000000) (41861302264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1212165525737271 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36133214363 / 1000000000000) (36133301351 / 1000000000000), orderedInterval (-28258158315 / 1000000000000) (-28258071327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (758516903356413 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54475620428 / 1000000000000) (54475625127 / 1000000000000), orderedInterval (-19881401274 / 1000000000000) (-19881396575 / 1000000000000)))) (orderedInterval (-1115622161 / 1000000000000) (-1115616996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (407932913338371 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (62141778535 / 1000000000000) (62141842816 / 1000000000000), orderedInterval (-49097866612 / 1000000000000) (-49097802331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1107617213968113 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45176412041 / 1000000000000) (45176412043 / 1000000000000), orderedInterval (15985457127 / 1000000000000) (15985457128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1512356612565201 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39048983964 / 1000000000000) (39048992689 / 1000000000000), orderedInterval (-12659477732 / 1000000000000) (-12659469007 / 1000000000000)))) (orderedInterval (-5165038119 / 1000000000000) (-5165036221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (639483096643587 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26544746819 / 1000000000000) (-26544746818 / 1000000000000), orderedInterval (-57166250038 / 1000000000000) (-57166250037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2599463284816227 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10477514963 / 1000000000000) (-10477514962 / 1000000000000), orderedInterval (-29484974518 / 1000000000000) (-29484974517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1736321004565293 / 4000000000000) 0 (IntervalRat.scale (699 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37150450921 / 1000000000000) (37150450931 / 1000000000000), orderedInterval (9254400171 / 1000000000000) (9254400181 / 1000000000000)))) (orderedInterval (-6277542237 / 1000000000000) (-6277542138 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks0 :
    compactCertificate478.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate478.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate478_chunkChecks0_0
    compactCertificate478_chunkChecks0_1 compactCertificate478_chunkChecks0_2

theorem compactCertificate478_chunkChecks1_0 :
    compactCertificate478.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (699 / 2) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42679060318 / 1000000000000) (-42679060128 / 1000000000000), orderedInterval (-47363610 / 1000000000000) (-47363420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1029760472582799 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28668002130 / 1000000000000) (28668002131 / 1000000000000), orderedInterval (40577215361 / 1000000000000) (40577215362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (333003379069167 / 800000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27848925451 / 1000000000000) (27848943931 / 1000000000000), orderedInterval (-27489574100 / 1000000000000) (-27489555620 / 1000000000000)))) (orderedInterval (-1661489964 / 1000000000000) (-1661488569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (300481537640493 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44609905988 / 1000000000000) (44609905989 / 1000000000000), orderedInterval (80230828180 / 1000000000000) (80230828181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (807135676326921 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56053829145 / 1000000000000) (56053829172 / 1000000000000), orderedInterval (3455064589 / 1000000000000) (3455064616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2191530371477157 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30546573514 / 1000000000000) (30546649432 / 1000000000000), orderedInterval (-15156299071 / 1000000000000) (-15156223153 / 1000000000000)))) (orderedInterval (1574772866 / 1000000000000) (1574781375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1614271352654541 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31418532105 / 1000000000000) (31418590499 / 1000000000000), orderedInterval (-24336127148 / 1000000000000) (-24336068755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2766081477147393 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27758767290 / 1000000000000) (27758767295 / 1000000000000), orderedInterval (12229807830 / 1000000000000) (12229807836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2037483096643587 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33174347667 / 1000000000000) (33174347671 / 1000000000000), orderedInterval (12185384057 / 1000000000000) (12185384061 / 1000000000000)))) (orderedInterval (-317152183 / 1000000000000) (-317152148 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks1_1 :
    compactCertificate478.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3126023032544301 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-982357944 / 1000000000000) (-982357943 / 1000000000000), orderedInterval (-28523778060 / 1000000000000) (-28523778059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1804810239332229 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14684966556 / 1000000000000) (-14684966373 / 1000000000000), orderedInterval (34589274541 / 1000000000000) (34589274725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3202667441089161 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9562262882 / 1000000000000) (-9562262881 / 1000000000000), orderedInterval (-26520905083 / 1000000000000) (-26520905082 / 1000000000000)))) (orderedInterval (6004768203 / 1000000000000) (6004768509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2992347362559309 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26894251591 / 1000000000000) (26894251602 / 1000000000000), orderedInterval (11282301286 / 1000000000000) (11282301297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2135480273848797 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19053635104 / 1000000000000) (19053635105 / 1000000000000), orderedInterval (28781828784 / 1000000000000) (28781828785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2421407028980763 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6138336490 / 1000000000000) (6138336492 / 1000000000000), orderedInterval (-31848025258 / 1000000000000) (-31848025256 / 1000000000000)))) (orderedInterval (4000639645 / 1000000000000) (4000639714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2018716736391147 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11578882324 / 1000000000000) (11578882371 / 1000000000000), orderedInterval (-33587721279 / 1000000000000) (-33587721232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1783597458138087 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20654231948 / 1000000000000) (20654231949 / 1000000000000), orderedInterval (31617380404 / 1000000000000) (31617380405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (516956062418613 / 800000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5860123998 / 1000000000000) (-5860123996 / 1000000000000), orderedInterval (30840248057 / 1000000000000) (30840248059 / 1000000000000)))) (orderedInterval (-1408525972 / 1000000000000) (-1408525922 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks1_2 :
    compactCertificate478.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1429927674556911 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5278219692 / 1000000000000) (5278219693 / 1000000000000), orderedInterval (41861302263 / 1000000000000) (41861302264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1212165525737271 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36133214363 / 1000000000000) (36133301351 / 1000000000000), orderedInterval (-28258158315 / 1000000000000) (-28258071327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (758516903356413 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54475620428 / 1000000000000) (54475625127 / 1000000000000), orderedInterval (-19881401274 / 1000000000000) (-19881396575 / 1000000000000)))) (orderedInterval (-5810547080 / 1000000000000) (-5810542647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (407932913338371 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (62141778535 / 1000000000000) (62141842816 / 1000000000000), orderedInterval (-49097866612 / 1000000000000) (-49097802331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1107617213968113 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45176412041 / 1000000000000) (45176412043 / 1000000000000), orderedInterval (15985457127 / 1000000000000) (15985457128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1512356612565201 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39048983964 / 1000000000000) (39048992689 / 1000000000000), orderedInterval (-12659477732 / 1000000000000) (-12659469007 / 1000000000000)))) (orderedInterval (1026782450 / 1000000000000) (1026783557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (639483096643587 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26544746819 / 1000000000000) (-26544746818 / 1000000000000), orderedInterval (-57166250038 / 1000000000000) (-57166250037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2599463284816227 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10477514963 / 1000000000000) (-10477514962 / 1000000000000), orderedInterval (-29484974518 / 1000000000000) (-29484974517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1736321004565293 / 4000000000000) 1 (IntervalRat.scale (699 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37150450921 / 1000000000000) (37150450931 / 1000000000000), orderedInterval (9254400171 / 1000000000000) (9254400181 / 1000000000000)))) (orderedInterval (2148622237 / 1000000000000) (2148622376 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks1 :
    compactCertificate478.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate478.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate478_chunkChecks1_0
    compactCertificate478_chunkChecks1_1 compactCertificate478_chunkChecks1_2

theorem compactCertificate478_chunkChecks2_0 :
    compactCertificate478.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (699 / 2) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42679060318 / 1000000000000) (-42679060128 / 1000000000000), orderedInterval (-47363610 / 1000000000000) (-47363420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1029760472582799 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28668002130 / 1000000000000) (28668002131 / 1000000000000), orderedInterval (40577215361 / 1000000000000) (40577215362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (333003379069167 / 800000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27848925451 / 1000000000000) (27848943931 / 1000000000000), orderedInterval (-27489574100 / 1000000000000) (-27489555620 / 1000000000000)))) (orderedInterval (14458212062 / 1000000000000) (14458213711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (300481537640493 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44609905988 / 1000000000000) (44609905989 / 1000000000000), orderedInterval (80230828180 / 1000000000000) (80230828181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (807135676326921 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56053829145 / 1000000000000) (56053829172 / 1000000000000), orderedInterval (3455064589 / 1000000000000) (3455064616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2191530371477157 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30546573514 / 1000000000000) (30546649432 / 1000000000000), orderedInterval (-15156299071 / 1000000000000) (-15156223153 / 1000000000000)))) (orderedInterval (4672058922 / 1000000000000) (4672072276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1614271352654541 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31418532105 / 1000000000000) (31418590499 / 1000000000000), orderedInterval (-24336127148 / 1000000000000) (-24336068755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2766081477147393 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27758767290 / 1000000000000) (27758767295 / 1000000000000), orderedInterval (12229807830 / 1000000000000) (12229807836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2037483096643587 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33174347667 / 1000000000000) (33174347671 / 1000000000000), orderedInterval (12185384057 / 1000000000000) (12185384061 / 1000000000000)))) (orderedInterval (1649761804 / 1000000000000) (1649761866 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks2_1 :
    compactCertificate478.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3126023032544301 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-982357944 / 1000000000000) (-982357943 / 1000000000000), orderedInterval (-28523778060 / 1000000000000) (-28523778059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1804810239332229 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14684966556 / 1000000000000) (-14684966373 / 1000000000000), orderedInterval (34589274541 / 1000000000000) (34589274725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3202667441089161 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9562262882 / 1000000000000) (-9562262881 / 1000000000000), orderedInterval (-26520905083 / 1000000000000) (-26520905082 / 1000000000000)))) (orderedInterval (8057474208 / 1000000000000) (8057474848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2992347362559309 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26894251591 / 1000000000000) (26894251602 / 1000000000000), orderedInterval (11282301286 / 1000000000000) (11282301297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2135480273848797 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19053635104 / 1000000000000) (19053635105 / 1000000000000), orderedInterval (28781828784 / 1000000000000) (28781828785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2421407028980763 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6138336490 / 1000000000000) (6138336492 / 1000000000000), orderedInterval (-31848025258 / 1000000000000) (-31848025256 / 1000000000000)))) (orderedInterval (-1897938290 / 1000000000000) (-1897938177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2018716736391147 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11578882324 / 1000000000000) (11578882371 / 1000000000000), orderedInterval (-33587721279 / 1000000000000) (-33587721232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1783597458138087 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20654231948 / 1000000000000) (20654231949 / 1000000000000), orderedInterval (31617380404 / 1000000000000) (31617380405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (516956062418613 / 800000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5860123998 / 1000000000000) (-5860123996 / 1000000000000), orderedInterval (30840248057 / 1000000000000) (30840248059 / 1000000000000)))) (orderedInterval (2162063258 / 1000000000000) (2162063332 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks2_2 :
    compactCertificate478.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1429927674556911 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5278219692 / 1000000000000) (5278219693 / 1000000000000), orderedInterval (41861302263 / 1000000000000) (41861302264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1212165525737271 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36133214363 / 1000000000000) (36133301351 / 1000000000000), orderedInterval (-28258158315 / 1000000000000) (-28258071327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (758516903356413 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54475620428 / 1000000000000) (54475625127 / 1000000000000), orderedInterval (-19881401274 / 1000000000000) (-19881396575 / 1000000000000)))) (orderedInterval (1915038475 / 1000000000000) (1915042312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (407932913338371 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (62141778535 / 1000000000000) (62141842816 / 1000000000000), orderedInterval (-49097866612 / 1000000000000) (-49097802331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1107617213968113 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45176412041 / 1000000000000) (45176412043 / 1000000000000), orderedInterval (15985457127 / 1000000000000) (15985457128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1512356612565201 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39048983964 / 1000000000000) (39048992689 / 1000000000000), orderedInterval (-12659477732 / 1000000000000) (-12659469007 / 1000000000000)))) (orderedInterval (4240415360 / 1000000000000) (4240416285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (639483096643587 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26544746819 / 1000000000000) (-26544746818 / 1000000000000), orderedInterval (-57166250038 / 1000000000000) (-57166250037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2599463284816227 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10477514963 / 1000000000000) (-10477514962 / 1000000000000), orderedInterval (-29484974518 / 1000000000000) (-29484974517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1736321004565293 / 4000000000000) 2 (IntervalRat.scale (699 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37150450921 / 1000000000000) (37150450931 / 1000000000000), orderedInterval (9254400171 / 1000000000000) (9254400181 / 1000000000000)))) (orderedInterval (7830901190 / 1000000000000) (7830901394 / 1000000000000))) = true
  rfl'

theorem compactCertificate478_chunkChecks2 :
    compactCertificate478.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate478.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate478_chunkChecks2_0
    compactCertificate478_chunkChecks2_1 compactCertificate478_chunkChecks2_2

theorem compactCertificate478_chunkChecks3_0 :
    compactCertificate478.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (699 / 2) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42679060318 / 1000000000000) (-42679060128 / 1000000000000), orderedInterval (-47363610 / 1000000000000) (-47363420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1029760472582799 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28668002130 / 1000000000000) (28668002131 / 1000000000000), orderedInterval (40577215361 / 1000000000000) (40577215362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (333003379069167 / 800000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27848925451 / 1000000000000) (27848943931 / 1000000000000), orderedInterval (-27489574100 / 1000000000000) (-27489555620 / 1000000000000)))) (orderedInterval (2551495160 / 1000000000000) (2551497109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (300481537640493 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44609905988 / 1000000000000) (44609905989 / 1000000000000), orderedInterval (80230828180 / 1000000000000) (80230828181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (807135676326921 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56053829145 / 1000000000000) (56053829172 / 1000000000000), orderedInterval (3455064589 / 1000000000000) (3455064616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2191530371477157 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30546573514 / 1000000000000) (30546649432 / 1000000000000), orderedInterval (-15156299071 / 1000000000000) (-15156223153 / 1000000000000)))) (orderedInterval (-4179680985 / 1000000000000) (-4179660057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1614271352654541 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31418532105 / 1000000000000) (31418590499 / 1000000000000), orderedInterval (-24336127148 / 1000000000000) (-24336068755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2766081477147393 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27758767290 / 1000000000000) (27758767295 / 1000000000000), orderedInterval (12229807830 / 1000000000000) (12229807836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2037483096643587 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33174347667 / 1000000000000) (33174347671 / 1000000000000), orderedInterval (12185384057 / 1000000000000) (12185384061 / 1000000000000)))) (orderedInterval (2005489233 / 1000000000000) (2005489346 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate478_chunkChecks3_1 :
    compactCertificate478.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3126023032544301 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-982357944 / 1000000000000) (-982357943 / 1000000000000), orderedInterval (-28523778060 / 1000000000000) (-28523778059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1804810239332229 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14684966556 / 1000000000000) (-14684966373 / 1000000000000), orderedInterval (34589274541 / 1000000000000) (34589274725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3202667441089161 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9562262882 / 1000000000000) (-9562262881 / 1000000000000), orderedInterval (-26520905083 / 1000000000000) (-26520905082 / 1000000000000)))) (orderedInterval (-16874824796 / 1000000000000) (-16874823414 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2992347362559309 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26894251591 / 1000000000000) (26894251602 / 1000000000000), orderedInterval (11282301286 / 1000000000000) (11282301297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2135480273848797 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19053635104 / 1000000000000) (19053635105 / 1000000000000), orderedInterval (28781828784 / 1000000000000) (28781828785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2421407028980763 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6138336490 / 1000000000000) (6138336492 / 1000000000000), orderedInterval (-31848025258 / 1000000000000) (-31848025256 / 1000000000000)))) (orderedInterval (-8535328764 / 1000000000000) (-8535328572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2018716736391147 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11578882324 / 1000000000000) (11578882371 / 1000000000000), orderedInterval (-33587721279 / 1000000000000) (-33587721232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1783597458138087 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20654231948 / 1000000000000) (20654231949 / 1000000000000), orderedInterval (31617380404 / 1000000000000) (31617380405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (516956062418613 / 800000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5860123998 / 1000000000000) (-5860123996 / 1000000000000), orderedInterval (30840248057 / 1000000000000) (30840248059 / 1000000000000)))) (orderedInterval (-71762752 / 1000000000000) (-71762638 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate478_chunkChecks3_2 :
    compactCertificate478.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1429927674556911 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5278219692 / 1000000000000) (5278219693 / 1000000000000), orderedInterval (41861302263 / 1000000000000) (41861302264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1212165525737271 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36133214363 / 1000000000000) (36133301351 / 1000000000000), orderedInterval (-28258158315 / 1000000000000) (-28258071327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (758516903356413 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54475620428 / 1000000000000) (54475625127 / 1000000000000), orderedInterval (-19881401274 / 1000000000000) (-19881396575 / 1000000000000)))) (orderedInterval (6217684993 / 1000000000000) (6217688314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (407932913338371 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (62141778535 / 1000000000000) (62141842816 / 1000000000000), orderedInterval (-49097866612 / 1000000000000) (-49097802331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1107617213968113 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45176412041 / 1000000000000) (45176412043 / 1000000000000), orderedInterval (15985457127 / 1000000000000) (15985457128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1512356612565201 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39048983964 / 1000000000000) (39048992689 / 1000000000000), orderedInterval (-12659477732 / 1000000000000) (-12659469007 / 1000000000000)))) (orderedInterval (-1082590670 / 1000000000000) (-1082589752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (639483096643587 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26544746819 / 1000000000000) (-26544746818 / 1000000000000), orderedInterval (-57166250038 / 1000000000000) (-57166250037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2599463284816227 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10477514963 / 1000000000000) (-10477514962 / 1000000000000), orderedInterval (-29484974518 / 1000000000000) (-29484974517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1736321004565293 / 4000000000000) 3 (IntervalRat.scale (699 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37150450921 / 1000000000000) (37150450931 / 1000000000000), orderedInterval (9254400171 / 1000000000000) (9254400181 / 1000000000000)))) (orderedInterval (-12092662798 / 1000000000000) (-12092662484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate478_chunkChecks3 :
    compactCertificate478.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate478.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate478_chunkChecks3_0
    compactCertificate478_chunkChecks3_1 compactCertificate478_chunkChecks3_2

theorem compactCertificate478_chunkChecks4_0 :
    compactCertificate478.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (699 / 2) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42679060318 / 1000000000000) (-42679060128 / 1000000000000), orderedInterval (-47363610 / 1000000000000) (-47363420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1029760472582799 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (28668002130 / 1000000000000) (28668002131 / 1000000000000), orderedInterval (40577215361 / 1000000000000) (40577215362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (333003379069167 / 800000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27848925451 / 1000000000000) (27848943931 / 1000000000000), orderedInterval (-27489574100 / 1000000000000) (-27489555620 / 1000000000000)))) (orderedInterval (-13564169181 / 1000000000000) (-13564166869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (300481537640493 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44609905988 / 1000000000000) (44609905989 / 1000000000000), orderedInterval (80230828180 / 1000000000000) (80230828181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (807135676326921 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56053829145 / 1000000000000) (56053829172 / 1000000000000), orderedInterval (3455064589 / 1000000000000) (3455064616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2191530371477157 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30546573514 / 1000000000000) (30546649432 / 1000000000000), orderedInterval (-15156299071 / 1000000000000) (-15156223153 / 1000000000000)))) (orderedInterval (-12863553861 / 1000000000000) (-12863520998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1614271352654541 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31418532105 / 1000000000000) (31418590499 / 1000000000000), orderedInterval (-24336127148 / 1000000000000) (-24336068755 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2766081477147393 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27758767290 / 1000000000000) (27758767295 / 1000000000000), orderedInterval (12229807830 / 1000000000000) (12229807836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2037483096643587 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33174347667 / 1000000000000) (33174347671 / 1000000000000), orderedInterval (12185384057 / 1000000000000) (12185384061 / 1000000000000)))) (orderedInterval (-9516170962 / 1000000000000) (-9516170755 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate478_chunkChecks4_1 :
    compactCertificate478.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3126023032544301 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-982357944 / 1000000000000) (-982357943 / 1000000000000), orderedInterval (-28523778060 / 1000000000000) (-28523778059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1804810239332229 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14684966556 / 1000000000000) (-14684966373 / 1000000000000), orderedInterval (34589274541 / 1000000000000) (34589274725 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3202667441089161 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9562262882 / 1000000000000) (-9562262881 / 1000000000000), orderedInterval (-26520905083 / 1000000000000) (-26520905082 / 1000000000000)))) (orderedInterval (-36002585350 / 1000000000000) (-36002582310 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2992347362559309 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26894251591 / 1000000000000) (26894251602 / 1000000000000), orderedInterval (11282301286 / 1000000000000) (11282301297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2135480273848797 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (19053635104 / 1000000000000) (19053635105 / 1000000000000), orderedInterval (28781828784 / 1000000000000) (28781828785 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2421407028980763 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6138336490 / 1000000000000) (6138336492 / 1000000000000), orderedInterval (-31848025258 / 1000000000000) (-31848025256 / 1000000000000)))) (orderedInterval (-612443326 / 1000000000000) (-612442991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2018716736391147 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (11578882324 / 1000000000000) (11578882371 / 1000000000000), orderedInterval (-33587721279 / 1000000000000) (-33587721232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1783597458138087 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20654231948 / 1000000000000) (20654231949 / 1000000000000), orderedInterval (31617380404 / 1000000000000) (31617380405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (516956062418613 / 800000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5860123998 / 1000000000000) (-5860123996 / 1000000000000), orderedInterval (30840248057 / 1000000000000) (30840248059 / 1000000000000)))) (orderedInterval (-4303221216 / 1000000000000) (-4303221037 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate478_chunkChecks4_2 :
    compactCertificate478.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1429927674556911 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (5278219692 / 1000000000000) (5278219693 / 1000000000000), orderedInterval (41861302263 / 1000000000000) (41861302264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1212165525737271 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36133214363 / 1000000000000) (36133301351 / 1000000000000), orderedInterval (-28258158315 / 1000000000000) (-28258071327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (758516903356413 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54475620428 / 1000000000000) (54475625127 / 1000000000000), orderedInterval (-19881401274 / 1000000000000) (-19881396575 / 1000000000000)))) (orderedInterval (-1961556599 / 1000000000000) (-1961553710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (407932913338371 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (62141778535 / 1000000000000) (62141842816 / 1000000000000), orderedInterval (-49097866612 / 1000000000000) (-49097802331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1107617213968113 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45176412041 / 1000000000000) (45176412043 / 1000000000000), orderedInterval (15985457127 / 1000000000000) (15985457128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1512356612565201 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39048983964 / 1000000000000) (39048992689 / 1000000000000), orderedInterval (-12659477732 / 1000000000000) (-12659469007 / 1000000000000)))) (orderedInterval (-4504644488 / 1000000000000) (-4504643518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (639483096643587 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26544746819 / 1000000000000) (-26544746818 / 1000000000000), orderedInterval (-57166250038 / 1000000000000) (-57166250037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2599463284816227 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10477514963 / 1000000000000) (-10477514962 / 1000000000000), orderedInterval (-29484974518 / 1000000000000) (-29484974517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1736321004565293 / 4000000000000) 4 (IntervalRat.scale (699 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37150450921 / 1000000000000) (37150450931 / 1000000000000), orderedInterval (9254400171 / 1000000000000) (9254400181 / 1000000000000)))) (orderedInterval (-6328791583 / 1000000000000) (-6328791080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate478_chunkChecks4 :
    compactCertificate478.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate478.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate478_chunkChecks4_0
    compactCertificate478_chunkChecks4_1 compactCertificate478_chunkChecks4_2

theorem compactCertificate478_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate478.chunkCheck r b = true :=
  compactCertificate478.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate478_chunkChecks0
    · exact compactCertificate478_chunkChecks1
    · exact compactCertificate478_chunkChecks2
    · exact compactCertificate478_chunkChecks3
    · exact compactCertificate478_chunkChecks4)

theorem compactCertificate478_coefficient0 :
    compactCertificate478.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate478_coefficient1 :
    compactCertificate478.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate478_coefficient2 :
    compactCertificate478.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate478_coefficient3 :
    compactCertificate478.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate478_coefficient4 :
    compactCertificate478.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate478_coefficients : ∀ r : Fin 5,
    compactCertificate478.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate478_coefficient0
  · exact compactCertificate478_coefficient1
  · exact compactCertificate478_coefficient2
  · exact compactCertificate478_coefficient3
  · exact compactCertificate478_coefficient4

theorem compactCertificate478_lower : (1 : ℚ) ≤ compactCertificate478.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate478, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate478_proves {t : ℝ} (ht : t ∈ compactCertificate478.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate478.proves compactCertificate478_states compactCertificate478_chunks
    compactCertificate478_coefficients compactCertificate478_lower ht

end Erdos232
