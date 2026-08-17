/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.Assembly
import ErdosProblems.Erdos622.TailoredTrichotomy

/-!
# The three uniform regimes for Erdős Problem 622

This file connects the quantitative predicates in the checked structural
trichotomy to the abstract three-case assembly interface.  The theorem is
pointwise in `n`, so its eventual form has no hidden lower threshold.
-/

namespace Erdos622

open Trichotomy TailoredTrichotomy

/-- The fixed-constant bi-dense branch of the DKM trichotomy. -/
def BiDenseRegime : GraphRegime :=
  fun n G => BiDense G n epsilon0

/-- The fixed-constant almost-two-cliques branch of the DKM trichotomy. -/
def AlmostTwoCliquesRegime : GraphRegime :=
  fun n G => AlmostTwoCliques G n epsilon0

/-- The fixed-constant almost-bipartite branch of the DKM trichotomy. -/
def AlmostBipartiteRegime : GraphRegime :=
  fun n G => AlmostBipartite G n epsilon0 gamma0

/-- The cleaned structural trichotomy in the exact form consumed by the
final density assembly. -/
theorem uniform_regime_trichotomy :
    UniformTrichotomy BiDenseRegime AlmostTwoCliquesRegime
      AlmostBipartiteRegime := by
  filter_upwards [] with n
  intro G hregular
  exact regular_dirac_trichotomy n G hregular

end Erdos622
