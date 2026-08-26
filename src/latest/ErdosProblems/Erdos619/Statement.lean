/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 619.
Informal proof: Claude Fable 5.
Formal proof: GPT-5.5 with Codex, following a formalization sketch and guidance
from Claude Fable 5. Human contributor and publisher: Nick (Nikolas) Kuhn.
Source: https://www.erdosproblems.com/619#post-6986
https://github.com/nick-kuhn/erdos-619/tree/7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f
Original Lean/Mathlib version: 4.28.0.
Original Mathlib revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import Mathlib

namespace Erdos619

/-- The minimum number of edges added while remaining triangle-free and reaching
extended diameter at most `r`. The infimum of the empty set is zero. -/
noncomputable def minNewEdges {V : Type*} (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ H : SimpleGraph V,
    G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ r ∧ (H \ G).edgeSet.ncard = k}

end Erdos619
