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
import ErdosProblems.Erdos76.LocalAveraging
import ErdosProblems.Erdos76.KahnDiscretization
import ErdosProblems.Erdos76.PippengerSpencerOuterIteration
import ErdosProblems.Erdos76.PippengerSpencerAllOrderZero
import ErdosProblems.Erdos76.StructuralAssembly
import ErdosProblems.Erdos76.NewAveraging
import ErdosProblems.Erdos76.UnconditionalRounding
import ErdosProblems.Erdos76.Assembly
import ErdosProblems.Erdos76.HaxellRodl

/-!
# Erdős Problem 76

In every red--blue colouring of the edges of `Kₙ`, there are asymptotically
at least `n² / 12` pairwise edge-disjoint monochromatic triangles.  We encode
a colouring by its red graph `G`; the blue graph is `Gᶜ`.

The main results are `erdos76`, in eventual-epsilon form, and `erdos_76`,
which explicitly produces a family of edge-disjoint monochromatic triangles.
The proof uses the new weighted counting inequality and finite LP duality to
obtain the explicit fractional bound `n² / 12 - n / 2`, then the fully proved
Haxell–Rödl transference theorem. The latter is derived from capped LP duality,
triangle removal, and unconditional weighted hypergraph matching. The older structural
assembly lemmas below are retained for compatibility but are not hypotheses
or dependencies of the new argument.

Reference: V. Gruslys and S. Letzter, *Monochromatic triangle packings in
red-blue graphs*, Combinatorics, Probability and Computing 31 (2022),
994--1027.
-/

namespace Erdos76

noncomputable section

/-- Unconditional asymptotic monochromatic triangle packing from the new
fractional argument and the proved rounding theorem. -/
theorem erdos76 : Resolution :=
  resolution_of_asymptotic_fractional NewProof.asymptotic_fractional haxellRodlRounding

/-- Erdős Problem 76, with the actual integral packing and the relative-error
form of the asymptotically sharp constant. -/
theorem erdos_76 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), ∃ P : Finset (Finset (Fin n)),
        (∀ t ∈ P, G.IsNClique 3 t ∨ Gᶜ.IsNClique 3 t) ∧
        EdgeDisjoint P ∧ (1 - ε) * (n : ℝ) ^ 2 / 12 ≤ (P.card : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (erdos76 (ε / 12) (by positivity))
  refine ⟨N, ?_⟩
  intro n hn G
  obtain ⟨P, hP, hcard⟩ := exists_max_monochromaticPacking G
  refine ⟨P, ?_, hP.2, ?_⟩
  · intro t ht
    exact mem_monochromaticTriangles.mp (hP.1 ht)
  · rw [hcard]
    convert hN n hn G using 1
    ring

/-- Once the two substantive ingredients are available, the exact
eventual-epsilon formulation of Erdős Problem 76 follows without any further
combinatorial loss. -/
theorem resolution_of_gruslysLetzterFractional_and_kahn
    (hGL : GruslysLetzterFractional) (hKahn : KahnWeightedMatching) :
    Resolution :=
  resolution_of_smoothed_fractional_and_kahn
    hGL.smoothedFractionalMonochromaticTriangles hKahn

/-- Assembly boundary after replacing the weighted rounding theorem by the
max-degree Pippenger--Spencer statement through integer-copy discretization. -/
theorem resolution_of_gruslysLetzterFractional_and_pippengerSpencer
    (hGL : GruslysLetzterFractional) (hPS : PippengerSpencerMatching) :
    Resolution :=
  resolution_of_gruslysLetzterFractional_and_kahn hGL
    (kahnWeightedMatching_of_multiplicative
      (pippengerSpencerMatching_to_kahnMultiplicative hPS))

/-- Fully expanded assembly boundary.  The four hypotheses are exactly the
remaining substantive theorems in the published proof: fractional stability,
the companion almost-complete decomposition theorem, the integral
almost-bipartite cross packing, and Pippenger--Spencer rounding. -/
theorem resolution_of_structural_components_and_pippengerSpencer
    (hstable : FractionalStabilityDichotomy)
    (hAC : AlmostCompleteFractionalDecomposition)
    (hcross : AlmostBipartiteIntegralCrossPacking)
    (hPS : PippengerSpencerMatching) : Resolution :=
  resolution_of_gruslysLetzterFractional_and_pippengerSpencer
    (gruslysLetzterFractional_of_integralCrossPacking hstable hAC hcross) hPS

/-- Assembly boundary with the stability theorem expanded into the finite
classification and the pentagon-extension table.  The human one-vertex
extension theorem is derived from the companion almost-complete theorem and
the now-proved matching-avoiding form of Proposition 4.2. -/
theorem resolution_of_finite_components_and_pippengerSpencer
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hAC : AlmostCompleteFractionalDecomposition)
    (hPS : PippengerSpencerMatching) : Resolution :=
  resolution_of_gruslysLetzterFractional_and_pippengerSpencer
    (gruslysLetzterFractional_of_finiteStructuralComponents
      hclass hpent hAC) hPS

/-- Current narrowest checked boundary: on the rounding side only the
standard near-regular Pippenger--Spencer chromatic-index theorem remains.  The
regular completion, restriction to original edges, largest-color-class step,
integer-copy discretization, and problem-specific transfer are all proved. -/
theorem resolution_of_finite_components_and_nearRegularEdgeColoring
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hAC : AlmostCompleteFractionalDecomposition)
    (hColor : NearRegularPippengerSpencerEdgeColoring) : Resolution :=
  resolution_of_finite_components_and_pippengerSpencer
    hclass hpent hAC
    (nearRegularPippengerSpencerEdgeColoring_to_pippengerSpencerMatching hColor)

/-- Rounding assembly boundary at the local-generator theorem used in the
Pippenger--Spencer nibble.  Fresh regular completions, finite local-lemma
batches, the scalar outer schedule, residual greedy colouring, and the
matching extraction from a colour class are all checked downstream of this
single two-sided inner-marginal hypothesis. -/
theorem resolution_of_finite_components_and_sharpInnerMarginal
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hAC : AlmostCompleteFractionalDecomposition)
    (hinner : FiniteHypergraph.SharpTwoSidedFixedLengthInnerMarginal) : Resolution :=
  resolution_of_finite_components_and_nearRegularEdgeColoring
    hclass hpent hAC
    (FiniteHypergraph.sharpTwoSidedFixedLengthInnerMarginal_to_nearRegular hinner)

/-- Minimal rounding assembly boundary: because every outer batch first uses a
fresh exact regular completion, it suffices to prove the sharp local-generator
theorem on exactly regular hypergraphs. -/
theorem resolution_of_finite_components_and_exactRegularSharpInnerMarginal
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hAC : AlmostCompleteFractionalDecomposition)
    (hinner :
      FiniteHypergraph.SharpExactRegularTwoSidedFixedLengthInnerMarginal) :
    Resolution :=
  resolution_of_finite_components_and_nearRegularEdgeColoring
    hclass hpent hAC
    (FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular
      hinner)

/-- The sharp exact-regular local generator is now unconditional; only the
finite structural certificate inputs remain at this assembly boundary. -/
theorem resolution_of_finite_components
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hAC : AlmostCompleteFractionalDecomposition) : Resolution :=
  resolution_of_finite_components_and_exactRegularSharpInnerMarginal
    hclass hpent hAC
    FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal

/-- Narrowest checked boundary.  Exact companion bases through order ten,
the full companion structural induction D5--D8, all deterministic
regular-completion and rounding reductions, and all human stability induction
steps are discharged, as are Proposition 4.2 and the sharp two-sided
Pippenger--Spencer local marginal.  The hypotheses are precisely the remaining
strong finite certificates and the two finite stability inputs. -/
theorem resolution_of_remaining_components
    (hclass : FiniteStabilityClassification)
    (hpent : PentagonExtensionStep)
    (hbases : AlmostCompleteStrongCertificateBases) :
    Resolution :=
  resolution_of_gruslysLetzterFractional_and_pippengerSpencer
    (gruslysLetzterFractional_of_finiteComponents
      hclass hpent hbases)
    (nearRegularPippengerSpencerEdgeColoring_to_pippengerSpencerMatching
      (FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular
        FiniteHypergraph.sharpExactRegularTwoSidedFixedLengthInnerMarginal))

end

end Erdos76
