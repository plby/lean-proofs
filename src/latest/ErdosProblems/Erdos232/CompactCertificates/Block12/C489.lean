/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate489 : CompactCertificate where
  left := 360
  right := 361
  center := 721 / 2
  grid := fun i =>
    match i.val with
    | 0 => 115
    | 1 => 85
    | 2 => 137
    | 3 => 25
    | 4 => 66
    | 5 => 180
    | 6 => 133
    | 7 => 227
    | 8 => 167
    | 9 => 257
    | 10 => 148
    | 11 => 263
    | 12 => 246
    | 13 => 175
    | 14 => 199
    | 15 => 166
    | 16 => 146
    | 17 => 212
    | 18 => 117
    | 19 => 100
    | 20 => 62
    | 21 => 34
    | 22 => 91
    | 23 => 124
    | 24 => 53
    | 25 => 213
    | _ => 143
  point := fun i =>
    match i.val with
    | 0 => 721 / 2
    | 1 => 1062170673436621 / 4000000000000
    | 2 => 343484172115693 / 800000000000
    | 3 => 309938753417447 / 4000000000000
    | 4 => 832539088171259 / 4000000000000
    | 5 => 2260505576301903 / 4000000000000
    | 6 => 1665078176343239 / 4000000000000
    | 7 => 2853139835512547 / 4000000000000
    | 8 => 2101609889384873 / 4000000000000
    | 9 => 3224410023554279 / 4000000000000
    | 10 => 1861613995076591 / 4000000000000
    | 11 => 3303466702468219 / 4000000000000
    | 12 => 3086527107875911 / 4000000000000
    | 13 => 2202691384041463 / 4000000000000
    | 14 => 2497617264513777 / 4000000000000
    | 15 => 2082252885462113 / 4000000000000
    | 16 => 1839733572700373 / 4000000000000
    | 17 => 533226496428927 / 800000000000
    | 18 => 1474932551295469 / 4000000000000
    | 19 => 1250316658163909 / 4000000000000
    | 20 => 782390110615127 / 4000000000000
    | 21 => 420772003600809 / 4000000000000
    | 22 => 1142477841589427 / 4000000000000
    | 23 => 1559955819255379 / 4000000000000
    | 24 => 659609889384873 / 4000000000000
    | 25 => 2681277579903433 / 4000000000000
    | _ => 1790969162076647 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-79686573 / 1000000000000) (-79686571 / 1000000000000), orderedInterval (-42022870297 / 1000000000000) (-42022870295 / 1000000000000))
    | 1 => (orderedInterval (31833538170 / 1000000000000) (31833555219 / 1000000000000), orderedInterval (-37262841472 / 1000000000000) (-37262824423 / 1000000000000))
    | 2 => (orderedInterval (9819981987 / 1000000000000) (9819982014 / 1000000000000), orderedInterval (-37244529698 / 1000000000000) (-37244529671 / 1000000000000))
    | 3 => (orderedInterval (24294257072 / 1000000000000) (24294257464 / 1000000000000), orderedInterval (-87483776085 / 1000000000000) (-87483775693 / 1000000000000))
    | 4 => (orderedInterval (55304975955 / 1000000000000) (55304976032 / 1000000000000), orderedInterval (-335174734 / 1000000000000) (-335174657 / 1000000000000))
    | 5 => (orderedInterval (13835667040 / 1000000000000) (13835667041 / 1000000000000), orderedInterval (30566889923 / 1000000000000) (30566889924 / 1000000000000))
    | 6 => (orderedInterval (27424535880 / 1000000000000) (27424551839 / 1000000000000), orderedInterval (-27911963337 / 1000000000000) (-27911947378 / 1000000000000))
    | 7 => (orderedInterval (-23924283263 / 1000000000000) (-23924283262 / 1000000000000), orderedInterval (-17875874904 / 1000000000000) (-17875874903 / 1000000000000))
    | 8 => (orderedInterval (-34794414657 / 1000000000000) (-34794414228 / 1000000000000), orderedInterval (-980976190 / 1000000000000) (-980975760 / 1000000000000))
    | 9 => (orderedInterval (13511584256 / 1000000000000) (13511584316 / 1000000000000), orderedInterval (-24649557080 / 1000000000000) (-24649557020 / 1000000000000))
    | 10 => (orderedInterval (34893801478 / 1000000000000) (34893801482 / 1000000000000), orderedInterval (12222602552 / 1000000000000) (12222602556 / 1000000000000))
    | 11 => (orderedInterval (-11144792328 / 1000000000000) (-11144792327 / 1000000000000), orderedInterval (-25422453192 / 1000000000000) (-25422453191 / 1000000000000))
    | 12 => (orderedInterval (-11575169768 / 1000000000000) (-11575169746 / 1000000000000), orderedInterval (26295255951 / 1000000000000) (26295255972 / 1000000000000))
    | 13 => (orderedInterval (-33801152449 / 1000000000000) (-33801149896 / 1000000000000), orderedInterval (3712796673 / 1000000000000) (3712799226 / 1000000000000))
    | 14 => (orderedInterval (-401549788 / 1000000000000) (-401549787 / 1000000000000), orderedInterval (-31927761082 / 1000000000000) (-31927761081 / 1000000000000))
    | 15 => (orderedInterval (-5433352758 / 1000000000000) (-5433352755 / 1000000000000), orderedInterval (34551179623 / 1000000000000) (34551179626 / 1000000000000))
    | 16 => (orderedInterval (33082099035 / 1000000000000) (33082158058 / 1000000000000), orderedInterval (-17057411335 / 1000000000000) (-17057352312 / 1000000000000))
    | 17 => (orderedInterval (29784477751 / 1000000000000) (29784477792 / 1000000000000), orderedInterval (8224210438 / 1000000000000) (8224210480 / 1000000000000))
    | 18 => (orderedInterval (-38570794698 / 1000000000000) (-38570778321 / 1000000000000), orderedInterval (15505406565 / 1000000000000) (15505422942 / 1000000000000))
    | 19 => (orderedInterval (-32219507485 / 1000000000000) (-32219476594 / 1000000000000), orderedInterval (31651705323 / 1000000000000) (31651736214 / 1000000000000))
    | 20 => (orderedInterval (57019681051 / 1000000000000) (57019681156 / 1000000000000), orderedInterval (-2013591839 / 1000000000000) (-2013591733 / 1000000000000))
    | 21 => (orderedInterval (-57769372089 / 1000000000000) (-57769261770 / 1000000000000), orderedInterval (52376538566 / 1000000000000) (52376648884 / 1000000000000))
    | 22 => (orderedInterval (-23437429286 / 1000000000000) (-23437429285 / 1000000000000), orderedInterval (-40941864916 / 1000000000000) (-40941864915 / 1000000000000))
    | 23 => (orderedInterval (37894222454 / 1000000000000) (37894222456 / 1000000000000), orderedInterval (13966818887 / 1000000000000) (13966818889 / 1000000000000))
    | 24 => (orderedInterval (45313881693 / 1000000000000) (45313954392 / 1000000000000), orderedInterval (-42648970534 / 1000000000000) (-42648897834 / 1000000000000))
    | 25 => (orderedInterval (-28680854726 / 1000000000000) (-28680792544 / 1000000000000), orderedInterval (11296827975 / 1000000000000) (11296890157 / 1000000000000))
    | _ => (orderedInterval (24873272241 / 1000000000000) (24873280011 / 1000000000000), orderedInterval (-28367935880 / 1000000000000) (-28367928110 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (841289576 / 1000000000000) (841289763 / 1000000000000)
      | 1 => orderedInterval (772133141 / 1000000000000) (772133192 / 1000000000000)
      | 2 => orderedInterval (-102991746 / 1000000000000) (-102991715 / 1000000000000)
      | 3 => orderedInterval (-1399799812 / 1000000000000) (-1399799658 / 1000000000000)
      | 4 => orderedInterval (-2985334263 / 1000000000000) (-2985333978 / 1000000000000)
      | 5 => orderedInterval (-1193324277 / 1000000000000) (-1193320863 / 1000000000000)
      | 6 => orderedInterval (9847088017 / 1000000000000) (9847092478 / 1000000000000)
      | 7 => orderedInterval (-1305732509 / 1000000000000) (-1305730428 / 1000000000000)
      | _ => orderedInterval (-2059052773 / 1000000000000) (-2059045715 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-19515143529 / 1000000000000) (-19515143381 / 1000000000000)
      | 1 => orderedInterval (-3209478814 / 1000000000000) (-3209478761 / 1000000000000)
      | 2 => orderedInterval (1056374229 / 1000000000000) (1056374280 / 1000000000000)
      | 3 => orderedInterval (2683761553 / 1000000000000) (2683761873 / 1000000000000)
      | 4 => orderedInterval (-199938218 / 1000000000000) (-199937778 / 1000000000000)
      | 5 => orderedInterval (2210840443 / 1000000000000) (2210844804 / 1000000000000)
      | 6 => orderedInterval (-4124734173 / 1000000000000) (-4124729892 / 1000000000000)
      | 7 => orderedInterval (-704259754 / 1000000000000) (-704259121 / 1000000000000)
      | _ => orderedInterval (4783158276 / 1000000000000) (4783169840 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-892618645 / 1000000000000) (-892618523 / 1000000000000)
      | 1 => orderedInterval (1765043656 / 1000000000000) (1765043725 / 1000000000000)
      | 2 => orderedInterval (-1105605301 / 1000000000000) (-1105605216 / 1000000000000)
      | 3 => orderedInterval (16002568614 / 1000000000000) (16002569304 / 1000000000000)
      | 4 => orderedInterval (6495180961 / 1000000000000) (6495181643 / 1000000000000)
      | 5 => orderedInterval (599323665 / 1000000000000) (599329253 / 1000000000000)
      | 6 => orderedInterval (-8358134121 / 1000000000000) (-8358129974 / 1000000000000)
      | 7 => orderedInterval (2976081447 / 1000000000000) (2976081661 / 1000000000000)
      | _ => orderedInterval (-943374460 / 1000000000000) (-943354380 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (20489775319 / 1000000000000) (20489775424 / 1000000000000)
      | 1 => orderedInterval (8359032882 / 1000000000000) (8359032985 / 1000000000000)
      | 2 => orderedInterval (-4194352519 / 1000000000000) (-4194352373 / 1000000000000)
      | 3 => orderedInterval (-7511333522 / 1000000000000) (-7511332010 / 1000000000000)
      | 4 => orderedInterval (2546303347 / 1000000000000) (2546304409 / 1000000000000)
      | 5 => orderedInterval (-4561015785 / 1000000000000) (-4561008634 / 1000000000000)
      | 6 => orderedInterval (3854414431 / 1000000000000) (3854418463 / 1000000000000)
      | 7 => orderedInterval (908974760 / 1000000000000) (908974852 / 1000000000000)
      | _ => orderedInterval (-4258360927 / 1000000000000) (-4258325176 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (1101515222 / 1000000000000) (1101515318 / 1000000000000)
      | 1 => orderedInterval (-5762302835 / 1000000000000) (-5762302677 / 1000000000000)
      | 2 => orderedInterval (7538687220 / 1000000000000) (7538687479 / 1000000000000)
      | 3 => orderedInterval (-96434897280 / 1000000000000) (-96434893919 / 1000000000000)
      | 4 => orderedInterval (-13011751846 / 1000000000000) (-13011750179 / 1000000000000)
      | 5 => orderedInterval (3648335313 / 1000000000000) (3648344495 / 1000000000000)
      | 6 => orderedInterval (7920331876 / 1000000000000) (7920335830 / 1000000000000)
      | 7 => orderedInterval (-3765272300 / 1000000000000) (-3765272242 / 1000000000000)
      | _ => orderedInterval (16838726538 / 1000000000000) (16838791242 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2414275354 / 1000000000000) (2414293076 / 1000000000000)
    | 1 => orderedInterval (-17019419987 / 1000000000000) (-17019398136 / 1000000000000)
    | 2 => orderedInterval (16538465816 / 1000000000000) (16538497493 / 1000000000000)
    | 3 => orderedInterval (15633437986 / 1000000000000) (15633487940 / 1000000000000)
    | _ => orderedInterval (-81926628092 / 1000000000000) (-81926544653 / 1000000000000)

theorem compactCertificate489_stateChecks0 :
    compactCertificate489.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (721 / 2)) (orderedInterval (-79686573 / 1000000000000) (-79686571 / 1000000000000), orderedInterval (-42022870297 / 1000000000000) (-42022870295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1062170673436621 / 4000000000000)) (orderedInterval (31833538170 / 1000000000000) (31833555219 / 1000000000000), orderedInterval (-37262841472 / 1000000000000) (-37262824423 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (343484172115693 / 800000000000)) (orderedInterval (9819981987 / 1000000000000) (9819982014 / 1000000000000), orderedInterval (-37244529698 / 1000000000000) (-37244529671 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks1 :
    compactCertificate489.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (309938753417447 / 4000000000000)) (orderedInterval (24294257072 / 1000000000000) (24294257464 / 1000000000000), orderedInterval (-87483776085 / 1000000000000) (-87483775693 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (832539088171259 / 4000000000000)) (orderedInterval (55304975955 / 1000000000000) (55304976032 / 1000000000000), orderedInterval (-335174734 / 1000000000000) (-335174657 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2260505576301903 / 4000000000000)) (orderedInterval (13835667040 / 1000000000000) (13835667041 / 1000000000000), orderedInterval (30566889923 / 1000000000000) (30566889924 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks2 :
    compactCertificate489.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1665078176343239 / 4000000000000)) (orderedInterval (27424535880 / 1000000000000) (27424551839 / 1000000000000), orderedInterval (-27911963337 / 1000000000000) (-27911947378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2853139835512547 / 4000000000000)) (orderedInterval (-23924283263 / 1000000000000) (-23924283262 / 1000000000000), orderedInterval (-17875874904 / 1000000000000) (-17875874903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2101609889384873 / 4000000000000)) (orderedInterval (-34794414657 / 1000000000000) (-34794414228 / 1000000000000), orderedInterval (-980976190 / 1000000000000) (-980975760 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks3 :
    compactCertificate489.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3224410023554279 / 4000000000000)) (orderedInterval (13511584256 / 1000000000000) (13511584316 / 1000000000000), orderedInterval (-24649557080 / 1000000000000) (-24649557020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1861613995076591 / 4000000000000)) (orderedInterval (34893801478 / 1000000000000) (34893801482 / 1000000000000), orderedInterval (12222602552 / 1000000000000) (12222602556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (3303466702468219 / 4000000000000)) (orderedInterval (-11144792328 / 1000000000000) (-11144792327 / 1000000000000), orderedInterval (-25422453192 / 1000000000000) (-25422453191 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks4 :
    compactCertificate489.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3086527107875911 / 4000000000000)) (orderedInterval (-11575169768 / 1000000000000) (-11575169746 / 1000000000000), orderedInterval (26295255951 / 1000000000000) (26295255972 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2202691384041463 / 4000000000000)) (orderedInterval (-33801152449 / 1000000000000) (-33801149896 / 1000000000000), orderedInterval (3712796673 / 1000000000000) (3712799226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2497617264513777 / 4000000000000)) (orderedInterval (-401549788 / 1000000000000) (-401549787 / 1000000000000), orderedInterval (-31927761082 / 1000000000000) (-31927761081 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks5 :
    compactCertificate489.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2082252885462113 / 4000000000000)) (orderedInterval (-5433352758 / 1000000000000) (-5433352755 / 1000000000000), orderedInterval (34551179623 / 1000000000000) (34551179626 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1839733572700373 / 4000000000000)) (orderedInterval (33082099035 / 1000000000000) (33082158058 / 1000000000000), orderedInterval (-17057411335 / 1000000000000) (-17057352312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (533226496428927 / 800000000000)) (orderedInterval (29784477751 / 1000000000000) (29784477792 / 1000000000000), orderedInterval (8224210438 / 1000000000000) (8224210480 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks6 :
    compactCertificate489.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1474932551295469 / 4000000000000)) (orderedInterval (-38570794698 / 1000000000000) (-38570778321 / 1000000000000), orderedInterval (15505406565 / 1000000000000) (15505422942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1250316658163909 / 4000000000000)) (orderedInterval (-32219507485 / 1000000000000) (-32219476594 / 1000000000000), orderedInterval (31651705323 / 1000000000000) (31651736214 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (782390110615127 / 4000000000000)) (orderedInterval (57019681051 / 1000000000000) (57019681156 / 1000000000000), orderedInterval (-2013591839 / 1000000000000) (-2013591733 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks7 :
    compactCertificate489.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (420772003600809 / 4000000000000)) (orderedInterval (-57769372089 / 1000000000000) (-57769261770 / 1000000000000), orderedInterval (52376538566 / 1000000000000) (52376648884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1142477841589427 / 4000000000000)) (orderedInterval (-23437429286 / 1000000000000) (-23437429285 / 1000000000000), orderedInterval (-40941864916 / 1000000000000) (-40941864915 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1559955819255379 / 4000000000000)) (orderedInterval (37894222454 / 1000000000000) (37894222456 / 1000000000000), orderedInterval (13966818887 / 1000000000000) (13966818889 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_stateChecks8 :
    compactCertificate489.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (659609889384873 / 4000000000000)) (orderedInterval (45313881693 / 1000000000000) (45313954392 / 1000000000000), orderedInterval (-42648970534 / 1000000000000) (-42648897834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2681277579903433 / 4000000000000)) (orderedInterval (-28680854726 / 1000000000000) (-28680792544 / 1000000000000), orderedInterval (11296827975 / 1000000000000) (11296890157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1790969162076647 / 4000000000000)) (orderedInterval (24873272241 / 1000000000000) (24873280011 / 1000000000000), orderedInterval (-28367935880 / 1000000000000) (-28367928110 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_states : ∀ j,
    BesselStateValid (compactCertificate489.point j) (compactCertificate489.state j) :=
  compactCertificate489.statesValid_of_checks3 compactCertificate489_stateChecks0
    compactCertificate489_stateChecks1 compactCertificate489_stateChecks2
    compactCertificate489_stateChecks3 compactCertificate489_stateChecks4
    compactCertificate489_stateChecks5 compactCertificate489_stateChecks6
    compactCertificate489_stateChecks7 compactCertificate489_stateChecks8

theorem compactCertificate489_chunkChecks0_0 :
    compactCertificate489.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (721 / 2) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-79686573 / 1000000000000) (-79686571 / 1000000000000), orderedInterval (-42022870297 / 1000000000000) (-42022870295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1062170673436621 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31833538170 / 1000000000000) (31833555219 / 1000000000000), orderedInterval (-37262841472 / 1000000000000) (-37262824423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (343484172115693 / 800000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9819981987 / 1000000000000) (9819982014 / 1000000000000), orderedInterval (-37244529698 / 1000000000000) (-37244529671 / 1000000000000)))) (orderedInterval (841289576 / 1000000000000) (841289763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (309938753417447 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24294257072 / 1000000000000) (24294257464 / 1000000000000), orderedInterval (-87483776085 / 1000000000000) (-87483775693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (832539088171259 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55304975955 / 1000000000000) (55304976032 / 1000000000000), orderedInterval (-335174734 / 1000000000000) (-335174657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2260505576301903 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13835667040 / 1000000000000) (13835667041 / 1000000000000), orderedInterval (30566889923 / 1000000000000) (30566889924 / 1000000000000)))) (orderedInterval (772133141 / 1000000000000) (772133192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1665078176343239 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27424535880 / 1000000000000) (27424551839 / 1000000000000), orderedInterval (-27911963337 / 1000000000000) (-27911947378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2853139835512547 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23924283263 / 1000000000000) (-23924283262 / 1000000000000), orderedInterval (-17875874904 / 1000000000000) (-17875874903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2101609889384873 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34794414657 / 1000000000000) (-34794414228 / 1000000000000), orderedInterval (-980976190 / 1000000000000) (-980975760 / 1000000000000)))) (orderedInterval (-102991746 / 1000000000000) (-102991715 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks0_1 :
    compactCertificate489.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3224410023554279 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13511584256 / 1000000000000) (13511584316 / 1000000000000), orderedInterval (-24649557080 / 1000000000000) (-24649557020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1861613995076591 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34893801478 / 1000000000000) (34893801482 / 1000000000000), orderedInterval (12222602552 / 1000000000000) (12222602556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3303466702468219 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11144792328 / 1000000000000) (-11144792327 / 1000000000000), orderedInterval (-25422453192 / 1000000000000) (-25422453191 / 1000000000000)))) (orderedInterval (-1399799812 / 1000000000000) (-1399799658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3086527107875911 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11575169768 / 1000000000000) (-11575169746 / 1000000000000), orderedInterval (26295255951 / 1000000000000) (26295255972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2202691384041463 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33801152449 / 1000000000000) (-33801149896 / 1000000000000), orderedInterval (3712796673 / 1000000000000) (3712799226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2497617264513777 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-401549788 / 1000000000000) (-401549787 / 1000000000000), orderedInterval (-31927761082 / 1000000000000) (-31927761081 / 1000000000000)))) (orderedInterval (-2985334263 / 1000000000000) (-2985333978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2082252885462113 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5433352758 / 1000000000000) (-5433352755 / 1000000000000), orderedInterval (34551179623 / 1000000000000) (34551179626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1839733572700373 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33082099035 / 1000000000000) (33082158058 / 1000000000000), orderedInterval (-17057411335 / 1000000000000) (-17057352312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (533226496428927 / 800000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29784477751 / 1000000000000) (29784477792 / 1000000000000), orderedInterval (8224210438 / 1000000000000) (8224210480 / 1000000000000)))) (orderedInterval (-1193324277 / 1000000000000) (-1193320863 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks0_2 :
    compactCertificate489.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1474932551295469 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38570794698 / 1000000000000) (-38570778321 / 1000000000000), orderedInterval (15505406565 / 1000000000000) (15505422942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1250316658163909 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32219507485 / 1000000000000) (-32219476594 / 1000000000000), orderedInterval (31651705323 / 1000000000000) (31651736214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (782390110615127 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57019681051 / 1000000000000) (57019681156 / 1000000000000), orderedInterval (-2013591839 / 1000000000000) (-2013591733 / 1000000000000)))) (orderedInterval (9847088017 / 1000000000000) (9847092478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (420772003600809 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57769372089 / 1000000000000) (-57769261770 / 1000000000000), orderedInterval (52376538566 / 1000000000000) (52376648884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1142477841589427 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23437429286 / 1000000000000) (-23437429285 / 1000000000000), orderedInterval (-40941864916 / 1000000000000) (-40941864915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1559955819255379 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37894222454 / 1000000000000) (37894222456 / 1000000000000), orderedInterval (13966818887 / 1000000000000) (13966818889 / 1000000000000)))) (orderedInterval (-1305732509 / 1000000000000) (-1305730428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (659609889384873 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45313881693 / 1000000000000) (45313954392 / 1000000000000), orderedInterval (-42648970534 / 1000000000000) (-42648897834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2681277579903433 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28680854726 / 1000000000000) (-28680792544 / 1000000000000), orderedInterval (11296827975 / 1000000000000) (11296890157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1790969162076647 / 4000000000000) 0 (IntervalRat.scale (721 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24873272241 / 1000000000000) (24873280011 / 1000000000000), orderedInterval (-28367935880 / 1000000000000) (-28367928110 / 1000000000000)))) (orderedInterval (-2059052773 / 1000000000000) (-2059045715 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks0 :
    compactCertificate489.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate489.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate489_chunkChecks0_0
    compactCertificate489_chunkChecks0_1 compactCertificate489_chunkChecks0_2

theorem compactCertificate489_chunkChecks1_0 :
    compactCertificate489.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (721 / 2) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-79686573 / 1000000000000) (-79686571 / 1000000000000), orderedInterval (-42022870297 / 1000000000000) (-42022870295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1062170673436621 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31833538170 / 1000000000000) (31833555219 / 1000000000000), orderedInterval (-37262841472 / 1000000000000) (-37262824423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (343484172115693 / 800000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9819981987 / 1000000000000) (9819982014 / 1000000000000), orderedInterval (-37244529698 / 1000000000000) (-37244529671 / 1000000000000)))) (orderedInterval (-19515143529 / 1000000000000) (-19515143381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (309938753417447 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24294257072 / 1000000000000) (24294257464 / 1000000000000), orderedInterval (-87483776085 / 1000000000000) (-87483775693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (832539088171259 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55304975955 / 1000000000000) (55304976032 / 1000000000000), orderedInterval (-335174734 / 1000000000000) (-335174657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2260505576301903 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13835667040 / 1000000000000) (13835667041 / 1000000000000), orderedInterval (30566889923 / 1000000000000) (30566889924 / 1000000000000)))) (orderedInterval (-3209478814 / 1000000000000) (-3209478761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1665078176343239 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27424535880 / 1000000000000) (27424551839 / 1000000000000), orderedInterval (-27911963337 / 1000000000000) (-27911947378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2853139835512547 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23924283263 / 1000000000000) (-23924283262 / 1000000000000), orderedInterval (-17875874904 / 1000000000000) (-17875874903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2101609889384873 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34794414657 / 1000000000000) (-34794414228 / 1000000000000), orderedInterval (-980976190 / 1000000000000) (-980975760 / 1000000000000)))) (orderedInterval (1056374229 / 1000000000000) (1056374280 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks1_1 :
    compactCertificate489.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3224410023554279 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13511584256 / 1000000000000) (13511584316 / 1000000000000), orderedInterval (-24649557080 / 1000000000000) (-24649557020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1861613995076591 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34893801478 / 1000000000000) (34893801482 / 1000000000000), orderedInterval (12222602552 / 1000000000000) (12222602556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3303466702468219 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11144792328 / 1000000000000) (-11144792327 / 1000000000000), orderedInterval (-25422453192 / 1000000000000) (-25422453191 / 1000000000000)))) (orderedInterval (2683761553 / 1000000000000) (2683761873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3086527107875911 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11575169768 / 1000000000000) (-11575169746 / 1000000000000), orderedInterval (26295255951 / 1000000000000) (26295255972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2202691384041463 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33801152449 / 1000000000000) (-33801149896 / 1000000000000), orderedInterval (3712796673 / 1000000000000) (3712799226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2497617264513777 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-401549788 / 1000000000000) (-401549787 / 1000000000000), orderedInterval (-31927761082 / 1000000000000) (-31927761081 / 1000000000000)))) (orderedInterval (-199938218 / 1000000000000) (-199937778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2082252885462113 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5433352758 / 1000000000000) (-5433352755 / 1000000000000), orderedInterval (34551179623 / 1000000000000) (34551179626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1839733572700373 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33082099035 / 1000000000000) (33082158058 / 1000000000000), orderedInterval (-17057411335 / 1000000000000) (-17057352312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (533226496428927 / 800000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29784477751 / 1000000000000) (29784477792 / 1000000000000), orderedInterval (8224210438 / 1000000000000) (8224210480 / 1000000000000)))) (orderedInterval (2210840443 / 1000000000000) (2210844804 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks1_2 :
    compactCertificate489.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1474932551295469 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38570794698 / 1000000000000) (-38570778321 / 1000000000000), orderedInterval (15505406565 / 1000000000000) (15505422942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1250316658163909 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32219507485 / 1000000000000) (-32219476594 / 1000000000000), orderedInterval (31651705323 / 1000000000000) (31651736214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (782390110615127 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57019681051 / 1000000000000) (57019681156 / 1000000000000), orderedInterval (-2013591839 / 1000000000000) (-2013591733 / 1000000000000)))) (orderedInterval (-4124734173 / 1000000000000) (-4124729892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (420772003600809 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57769372089 / 1000000000000) (-57769261770 / 1000000000000), orderedInterval (52376538566 / 1000000000000) (52376648884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1142477841589427 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23437429286 / 1000000000000) (-23437429285 / 1000000000000), orderedInterval (-40941864916 / 1000000000000) (-40941864915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1559955819255379 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37894222454 / 1000000000000) (37894222456 / 1000000000000), orderedInterval (13966818887 / 1000000000000) (13966818889 / 1000000000000)))) (orderedInterval (-704259754 / 1000000000000) (-704259121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (659609889384873 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45313881693 / 1000000000000) (45313954392 / 1000000000000), orderedInterval (-42648970534 / 1000000000000) (-42648897834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2681277579903433 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28680854726 / 1000000000000) (-28680792544 / 1000000000000), orderedInterval (11296827975 / 1000000000000) (11296890157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1790969162076647 / 4000000000000) 1 (IntervalRat.scale (721 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24873272241 / 1000000000000) (24873280011 / 1000000000000), orderedInterval (-28367935880 / 1000000000000) (-28367928110 / 1000000000000)))) (orderedInterval (4783158276 / 1000000000000) (4783169840 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks1 :
    compactCertificate489.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate489.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate489_chunkChecks1_0
    compactCertificate489_chunkChecks1_1 compactCertificate489_chunkChecks1_2

theorem compactCertificate489_chunkChecks2_0 :
    compactCertificate489.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (721 / 2) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-79686573 / 1000000000000) (-79686571 / 1000000000000), orderedInterval (-42022870297 / 1000000000000) (-42022870295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1062170673436621 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31833538170 / 1000000000000) (31833555219 / 1000000000000), orderedInterval (-37262841472 / 1000000000000) (-37262824423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (343484172115693 / 800000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9819981987 / 1000000000000) (9819982014 / 1000000000000), orderedInterval (-37244529698 / 1000000000000) (-37244529671 / 1000000000000)))) (orderedInterval (-892618645 / 1000000000000) (-892618523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (309938753417447 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24294257072 / 1000000000000) (24294257464 / 1000000000000), orderedInterval (-87483776085 / 1000000000000) (-87483775693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (832539088171259 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55304975955 / 1000000000000) (55304976032 / 1000000000000), orderedInterval (-335174734 / 1000000000000) (-335174657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2260505576301903 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13835667040 / 1000000000000) (13835667041 / 1000000000000), orderedInterval (30566889923 / 1000000000000) (30566889924 / 1000000000000)))) (orderedInterval (1765043656 / 1000000000000) (1765043725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1665078176343239 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27424535880 / 1000000000000) (27424551839 / 1000000000000), orderedInterval (-27911963337 / 1000000000000) (-27911947378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2853139835512547 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23924283263 / 1000000000000) (-23924283262 / 1000000000000), orderedInterval (-17875874904 / 1000000000000) (-17875874903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2101609889384873 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34794414657 / 1000000000000) (-34794414228 / 1000000000000), orderedInterval (-980976190 / 1000000000000) (-980975760 / 1000000000000)))) (orderedInterval (-1105605301 / 1000000000000) (-1105605216 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks2_1 :
    compactCertificate489.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3224410023554279 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13511584256 / 1000000000000) (13511584316 / 1000000000000), orderedInterval (-24649557080 / 1000000000000) (-24649557020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1861613995076591 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34893801478 / 1000000000000) (34893801482 / 1000000000000), orderedInterval (12222602552 / 1000000000000) (12222602556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3303466702468219 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11144792328 / 1000000000000) (-11144792327 / 1000000000000), orderedInterval (-25422453192 / 1000000000000) (-25422453191 / 1000000000000)))) (orderedInterval (16002568614 / 1000000000000) (16002569304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3086527107875911 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11575169768 / 1000000000000) (-11575169746 / 1000000000000), orderedInterval (26295255951 / 1000000000000) (26295255972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2202691384041463 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33801152449 / 1000000000000) (-33801149896 / 1000000000000), orderedInterval (3712796673 / 1000000000000) (3712799226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2497617264513777 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-401549788 / 1000000000000) (-401549787 / 1000000000000), orderedInterval (-31927761082 / 1000000000000) (-31927761081 / 1000000000000)))) (orderedInterval (6495180961 / 1000000000000) (6495181643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2082252885462113 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5433352758 / 1000000000000) (-5433352755 / 1000000000000), orderedInterval (34551179623 / 1000000000000) (34551179626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1839733572700373 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33082099035 / 1000000000000) (33082158058 / 1000000000000), orderedInterval (-17057411335 / 1000000000000) (-17057352312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (533226496428927 / 800000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29784477751 / 1000000000000) (29784477792 / 1000000000000), orderedInterval (8224210438 / 1000000000000) (8224210480 / 1000000000000)))) (orderedInterval (599323665 / 1000000000000) (599329253 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks2_2 :
    compactCertificate489.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1474932551295469 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38570794698 / 1000000000000) (-38570778321 / 1000000000000), orderedInterval (15505406565 / 1000000000000) (15505422942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1250316658163909 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32219507485 / 1000000000000) (-32219476594 / 1000000000000), orderedInterval (31651705323 / 1000000000000) (31651736214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (782390110615127 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57019681051 / 1000000000000) (57019681156 / 1000000000000), orderedInterval (-2013591839 / 1000000000000) (-2013591733 / 1000000000000)))) (orderedInterval (-8358134121 / 1000000000000) (-8358129974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (420772003600809 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57769372089 / 1000000000000) (-57769261770 / 1000000000000), orderedInterval (52376538566 / 1000000000000) (52376648884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1142477841589427 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23437429286 / 1000000000000) (-23437429285 / 1000000000000), orderedInterval (-40941864916 / 1000000000000) (-40941864915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1559955819255379 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37894222454 / 1000000000000) (37894222456 / 1000000000000), orderedInterval (13966818887 / 1000000000000) (13966818889 / 1000000000000)))) (orderedInterval (2976081447 / 1000000000000) (2976081661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (659609889384873 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45313881693 / 1000000000000) (45313954392 / 1000000000000), orderedInterval (-42648970534 / 1000000000000) (-42648897834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2681277579903433 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28680854726 / 1000000000000) (-28680792544 / 1000000000000), orderedInterval (11296827975 / 1000000000000) (11296890157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1790969162076647 / 4000000000000) 2 (IntervalRat.scale (721 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24873272241 / 1000000000000) (24873280011 / 1000000000000), orderedInterval (-28367935880 / 1000000000000) (-28367928110 / 1000000000000)))) (orderedInterval (-943374460 / 1000000000000) (-943354380 / 1000000000000))) = true
  rfl'

theorem compactCertificate489_chunkChecks2 :
    compactCertificate489.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate489.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate489_chunkChecks2_0
    compactCertificate489_chunkChecks2_1 compactCertificate489_chunkChecks2_2

theorem compactCertificate489_chunkChecks3_0 :
    compactCertificate489.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (721 / 2) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-79686573 / 1000000000000) (-79686571 / 1000000000000), orderedInterval (-42022870297 / 1000000000000) (-42022870295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1062170673436621 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31833538170 / 1000000000000) (31833555219 / 1000000000000), orderedInterval (-37262841472 / 1000000000000) (-37262824423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (343484172115693 / 800000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9819981987 / 1000000000000) (9819982014 / 1000000000000), orderedInterval (-37244529698 / 1000000000000) (-37244529671 / 1000000000000)))) (orderedInterval (20489775319 / 1000000000000) (20489775424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (309938753417447 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24294257072 / 1000000000000) (24294257464 / 1000000000000), orderedInterval (-87483776085 / 1000000000000) (-87483775693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (832539088171259 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55304975955 / 1000000000000) (55304976032 / 1000000000000), orderedInterval (-335174734 / 1000000000000) (-335174657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2260505576301903 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13835667040 / 1000000000000) (13835667041 / 1000000000000), orderedInterval (30566889923 / 1000000000000) (30566889924 / 1000000000000)))) (orderedInterval (8359032882 / 1000000000000) (8359032985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1665078176343239 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27424535880 / 1000000000000) (27424551839 / 1000000000000), orderedInterval (-27911963337 / 1000000000000) (-27911947378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2853139835512547 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23924283263 / 1000000000000) (-23924283262 / 1000000000000), orderedInterval (-17875874904 / 1000000000000) (-17875874903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2101609889384873 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34794414657 / 1000000000000) (-34794414228 / 1000000000000), orderedInterval (-980976190 / 1000000000000) (-980975760 / 1000000000000)))) (orderedInterval (-4194352519 / 1000000000000) (-4194352373 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate489_chunkChecks3_1 :
    compactCertificate489.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3224410023554279 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13511584256 / 1000000000000) (13511584316 / 1000000000000), orderedInterval (-24649557080 / 1000000000000) (-24649557020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1861613995076591 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34893801478 / 1000000000000) (34893801482 / 1000000000000), orderedInterval (12222602552 / 1000000000000) (12222602556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3303466702468219 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11144792328 / 1000000000000) (-11144792327 / 1000000000000), orderedInterval (-25422453192 / 1000000000000) (-25422453191 / 1000000000000)))) (orderedInterval (-7511333522 / 1000000000000) (-7511332010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3086527107875911 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11575169768 / 1000000000000) (-11575169746 / 1000000000000), orderedInterval (26295255951 / 1000000000000) (26295255972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2202691384041463 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33801152449 / 1000000000000) (-33801149896 / 1000000000000), orderedInterval (3712796673 / 1000000000000) (3712799226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2497617264513777 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-401549788 / 1000000000000) (-401549787 / 1000000000000), orderedInterval (-31927761082 / 1000000000000) (-31927761081 / 1000000000000)))) (orderedInterval (2546303347 / 1000000000000) (2546304409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2082252885462113 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5433352758 / 1000000000000) (-5433352755 / 1000000000000), orderedInterval (34551179623 / 1000000000000) (34551179626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1839733572700373 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33082099035 / 1000000000000) (33082158058 / 1000000000000), orderedInterval (-17057411335 / 1000000000000) (-17057352312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (533226496428927 / 800000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29784477751 / 1000000000000) (29784477792 / 1000000000000), orderedInterval (8224210438 / 1000000000000) (8224210480 / 1000000000000)))) (orderedInterval (-4561015785 / 1000000000000) (-4561008634 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate489_chunkChecks3_2 :
    compactCertificate489.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1474932551295469 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38570794698 / 1000000000000) (-38570778321 / 1000000000000), orderedInterval (15505406565 / 1000000000000) (15505422942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1250316658163909 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32219507485 / 1000000000000) (-32219476594 / 1000000000000), orderedInterval (31651705323 / 1000000000000) (31651736214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (782390110615127 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57019681051 / 1000000000000) (57019681156 / 1000000000000), orderedInterval (-2013591839 / 1000000000000) (-2013591733 / 1000000000000)))) (orderedInterval (3854414431 / 1000000000000) (3854418463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (420772003600809 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57769372089 / 1000000000000) (-57769261770 / 1000000000000), orderedInterval (52376538566 / 1000000000000) (52376648884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1142477841589427 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23437429286 / 1000000000000) (-23437429285 / 1000000000000), orderedInterval (-40941864916 / 1000000000000) (-40941864915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1559955819255379 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37894222454 / 1000000000000) (37894222456 / 1000000000000), orderedInterval (13966818887 / 1000000000000) (13966818889 / 1000000000000)))) (orderedInterval (908974760 / 1000000000000) (908974852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (659609889384873 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45313881693 / 1000000000000) (45313954392 / 1000000000000), orderedInterval (-42648970534 / 1000000000000) (-42648897834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2681277579903433 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28680854726 / 1000000000000) (-28680792544 / 1000000000000), orderedInterval (11296827975 / 1000000000000) (11296890157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1790969162076647 / 4000000000000) 3 (IntervalRat.scale (721 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24873272241 / 1000000000000) (24873280011 / 1000000000000), orderedInterval (-28367935880 / 1000000000000) (-28367928110 / 1000000000000)))) (orderedInterval (-4258360927 / 1000000000000) (-4258325176 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate489_chunkChecks3 :
    compactCertificate489.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate489.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate489_chunkChecks3_0
    compactCertificate489_chunkChecks3_1 compactCertificate489_chunkChecks3_2

theorem compactCertificate489_chunkChecks4_0 :
    compactCertificate489.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (721 / 2) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-79686573 / 1000000000000) (-79686571 / 1000000000000), orderedInterval (-42022870297 / 1000000000000) (-42022870295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1062170673436621 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31833538170 / 1000000000000) (31833555219 / 1000000000000), orderedInterval (-37262841472 / 1000000000000) (-37262824423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (343484172115693 / 800000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9819981987 / 1000000000000) (9819982014 / 1000000000000), orderedInterval (-37244529698 / 1000000000000) (-37244529671 / 1000000000000)))) (orderedInterval (1101515222 / 1000000000000) (1101515318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (309938753417447 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24294257072 / 1000000000000) (24294257464 / 1000000000000), orderedInterval (-87483776085 / 1000000000000) (-87483775693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (832539088171259 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55304975955 / 1000000000000) (55304976032 / 1000000000000), orderedInterval (-335174734 / 1000000000000) (-335174657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2260505576301903 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (13835667040 / 1000000000000) (13835667041 / 1000000000000), orderedInterval (30566889923 / 1000000000000) (30566889924 / 1000000000000)))) (orderedInterval (-5762302835 / 1000000000000) (-5762302677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1665078176343239 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27424535880 / 1000000000000) (27424551839 / 1000000000000), orderedInterval (-27911963337 / 1000000000000) (-27911947378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2853139835512547 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23924283263 / 1000000000000) (-23924283262 / 1000000000000), orderedInterval (-17875874904 / 1000000000000) (-17875874903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2101609889384873 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34794414657 / 1000000000000) (-34794414228 / 1000000000000), orderedInterval (-980976190 / 1000000000000) (-980975760 / 1000000000000)))) (orderedInterval (7538687220 / 1000000000000) (7538687479 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate489_chunkChecks4_1 :
    compactCertificate489.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3224410023554279 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13511584256 / 1000000000000) (13511584316 / 1000000000000), orderedInterval (-24649557080 / 1000000000000) (-24649557020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1861613995076591 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34893801478 / 1000000000000) (34893801482 / 1000000000000), orderedInterval (12222602552 / 1000000000000) (12222602556 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3303466702468219 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11144792328 / 1000000000000) (-11144792327 / 1000000000000), orderedInterval (-25422453192 / 1000000000000) (-25422453191 / 1000000000000)))) (orderedInterval (-96434897280 / 1000000000000) (-96434893919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3086527107875911 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-11575169768 / 1000000000000) (-11575169746 / 1000000000000), orderedInterval (26295255951 / 1000000000000) (26295255972 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2202691384041463 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33801152449 / 1000000000000) (-33801149896 / 1000000000000), orderedInterval (3712796673 / 1000000000000) (3712799226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2497617264513777 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-401549788 / 1000000000000) (-401549787 / 1000000000000), orderedInterval (-31927761082 / 1000000000000) (-31927761081 / 1000000000000)))) (orderedInterval (-13011751846 / 1000000000000) (-13011750179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2082252885462113 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5433352758 / 1000000000000) (-5433352755 / 1000000000000), orderedInterval (34551179623 / 1000000000000) (34551179626 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1839733572700373 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33082099035 / 1000000000000) (33082158058 / 1000000000000), orderedInterval (-17057411335 / 1000000000000) (-17057352312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (533226496428927 / 800000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29784477751 / 1000000000000) (29784477792 / 1000000000000), orderedInterval (8224210438 / 1000000000000) (8224210480 / 1000000000000)))) (orderedInterval (3648335313 / 1000000000000) (3648344495 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate489_chunkChecks4_2 :
    compactCertificate489.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1474932551295469 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38570794698 / 1000000000000) (-38570778321 / 1000000000000), orderedInterval (15505406565 / 1000000000000) (15505422942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1250316658163909 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-32219507485 / 1000000000000) (-32219476594 / 1000000000000), orderedInterval (31651705323 / 1000000000000) (31651736214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (782390110615127 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57019681051 / 1000000000000) (57019681156 / 1000000000000), orderedInterval (-2013591839 / 1000000000000) (-2013591733 / 1000000000000)))) (orderedInterval (7920331876 / 1000000000000) (7920335830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (420772003600809 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-57769372089 / 1000000000000) (-57769261770 / 1000000000000), orderedInterval (52376538566 / 1000000000000) (52376648884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1142477841589427 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23437429286 / 1000000000000) (-23437429285 / 1000000000000), orderedInterval (-40941864916 / 1000000000000) (-40941864915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1559955819255379 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (37894222454 / 1000000000000) (37894222456 / 1000000000000), orderedInterval (13966818887 / 1000000000000) (13966818889 / 1000000000000)))) (orderedInterval (-3765272300 / 1000000000000) (-3765272242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (659609889384873 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (45313881693 / 1000000000000) (45313954392 / 1000000000000), orderedInterval (-42648970534 / 1000000000000) (-42648897834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2681277579903433 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28680854726 / 1000000000000) (-28680792544 / 1000000000000), orderedInterval (11296827975 / 1000000000000) (11296890157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1790969162076647 / 4000000000000) 4 (IntervalRat.scale (721 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (24873272241 / 1000000000000) (24873280011 / 1000000000000), orderedInterval (-28367935880 / 1000000000000) (-28367928110 / 1000000000000)))) (orderedInterval (16838726538 / 1000000000000) (16838791242 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate489_chunkChecks4 :
    compactCertificate489.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate489.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate489_chunkChecks4_0
    compactCertificate489_chunkChecks4_1 compactCertificate489_chunkChecks4_2

theorem compactCertificate489_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate489.chunkCheck r b = true :=
  compactCertificate489.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate489_chunkChecks0
    · exact compactCertificate489_chunkChecks1
    · exact compactCertificate489_chunkChecks2
    · exact compactCertificate489_chunkChecks3
    · exact compactCertificate489_chunkChecks4)

theorem compactCertificate489_coefficient0 :
    compactCertificate489.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate489_coefficient1 :
    compactCertificate489.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate489_coefficient2 :
    compactCertificate489.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate489_coefficient3 :
    compactCertificate489.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate489_coefficient4 :
    compactCertificate489.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate489_coefficients : ∀ r : Fin 5,
    compactCertificate489.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate489_coefficient0
  · exact compactCertificate489_coefficient1
  · exact compactCertificate489_coefficient2
  · exact compactCertificate489_coefficient3
  · exact compactCertificate489_coefficient4

theorem compactCertificate489_lower : (1 : ℚ) ≤ compactCertificate489.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate489, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate489_proves {t : ℝ} (ht : t ∈ compactCertificate489.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate489.proves compactCertificate489_states compactCertificate489_chunks
    compactCertificate489_coefficients compactCertificate489_lower ht

end Erdos232
