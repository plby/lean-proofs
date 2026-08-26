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
import ErdosProblems.Erdos76.AlmostComplete
import ErdosProblems.Erdos76.CertificateChecker

/-!
# Semantic bridge for finite Erdős 76 certificates

This deliberately tiny module keeps the executable certificate checker
independent of the later almost-complete-graph development.  It packages the
checker's raw soundness theorems into the semantic predicates used there.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace CertificateChecker
namespace PackingCert

noncomputable section

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- An accepted exact certificate is a fractional triangle decomposition. -/
theorem checkExact_sound_isFractionalDecomposition
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (c : PackingCert n) (hc : c.checkExact G = true) :
    IsFractionalDecomposition G c.weight := by
  have hs := checkExact_sound c hc
  constructor
  · exact hs.1
  · intro e he
    apply hs.2 e
    simpa [SimpleGraph.mem_edgeFinset] using he

/-- Rewriting the strong checker's objective as the uncovered-edge inequality
used by `HasStrongFractionalPacking`. -/
theorem checkStrong_sound_fractionalUncoveredWeight
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.checkStrong G a = true) :
    fractionalUncoveredWeight G c.weight ≤ (a : ℝ) := by
  have hsound := checkStrong_sound a c hc
  have huncovered :
      fractionalUncoveredWeight G c.weight =
        (G.edgeFinset.card : ℝ) - 3 * fractionalSize G c.weight := by
    rw [fractionalUncoveredWeight, Finset.sum_sub_distrib,
      sum_fractionalEdgeLoad_eq_three_mul_fractionalSize]
    simp only [Finset.sum_const, nsmul_one]
    congr 1
    norm_cast
    apply congrArg Finset.card
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [huncovered]
  by_cases ha : a ≤ G.edgeFinset.card
  · rw [Nat.cast_sub ha] at hsound
    linarith [hsound.2]
  · have hacard : (G.edgeFinset.card : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge ha))
    have hsize := fractionalSize_nonneg hsound.1
    linarith

/-- An accepted strong certificate witnesses the induction conclusion of the
Gruslys--Letzter almost-complete theorem. -/
theorem checkStrong_sound_hasStrongFractionalPacking
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a : ℕ) (c : PackingCert n) (hc : c.checkStrong G a = true) :
    HasStrongFractionalPacking G (a : ℝ) := by
  have hv := (checkStrong_eq_true_iff G a c).mp hc
  refine ⟨c.weight, hv.isFractionalPacking a c,
    checkStrong_sound_fractionalUncoveredWeight a c hc, ?_⟩
  intro t ht
  exact hv.weight_le_half a c t

end

end PackingCert
end CertificateChecker
end Erdos76
