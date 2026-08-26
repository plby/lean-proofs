/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Case T scan blocks (T-tail, part (i)), lines `e = 4`:
kernel-decided verification of `TlineGo 4 h a` for `a ≤ 3000`, chunked in
three per-line blocks of ≤ 1001 values each (cacheable, failure-localizing).
-/
import ErdosProblems.Erdos1112.Sharp.CaseTCore

namespace Erdos1112
namespace Proof

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_1_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 1 a = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_1_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 1 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_1_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 1 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,1)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_1 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 1 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_1_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_1_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_1_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_2_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 2 a = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_2_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 2 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_2_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 2 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,2)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_2 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 2 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_2_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_2_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_2_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_3_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 3 a = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_3_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 3 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_3_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 3 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,3)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_3 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 3 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_3_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_3_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_3_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_5_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 5 a = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_5_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 5 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_5_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 5 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,5)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_5 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 5 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_5_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_5_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_5_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_6_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 6 a = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_6_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 6 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_6_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 6 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,6)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_6 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 6 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_6_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_6_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_6_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_7_b0 : ∀ a : ℕ, a < 1000 → TlineGo 4 7 a = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_7_b1 : ∀ d : ℕ, d < 1000 → TlineGo 4 7 (1000 + d) = true := by decide

set_option maxHeartbeats 4000000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
set_option maxRecDepth 100000 in
theorem T_go_4_7_b2 : ∀ d : ℕ, d < 1001 → TlineGo 4 7 (2000 + d) = true := by decide

/-- Line `(e,h) = (4,7)`: the full scan `a ≤ 3000`. -/
theorem T_scan_4_7 : ∀ a : ℕ, a ≤ 3000 → TlineGo 4 7 a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 1000 with h1 | h1
  · exact T_go_4_7_b0 a h1
  · rcases Nat.lt_or_ge a 2000 with h2 | h2
    · have hd := T_go_4_7_b1 (a - 1000) (by omega)
      rwa [show 1000 + (a - 1000) = a from by omega] at hd
    · have hd := T_go_4_7_b2 (a - 2000) (by omega)
      rwa [show 2000 + (a - 2000) = a from by omega] at hd

end Proof
end Erdos1112
