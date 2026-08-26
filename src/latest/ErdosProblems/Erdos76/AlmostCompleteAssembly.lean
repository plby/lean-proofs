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
import ErdosProblems.Erdos76.AlmostCompleteStructuralStep
import ErdosProblems.Erdos76.CertificateExhaustionBridge

/-!
# Assembly of the almost-complete decomposition theorem

This file joins the kernel-checked exact certificate bases at orders `7`--`10`
to the strong certificate family at orders `11`--`13` and the structural
induction step.  In particular, it discharges the final passage from the
strong theorem with zero uncovered weight to an exact fractional
decomposition.
-/

namespace Erdos76

noncomputable section

/-- The still-data-dependent half of `AlmostCompleteCertificateBases`: the
strong finite certificate family at orders `11`, `12`, and `13`. -/
def AlmostCompleteStrongCertificateBases : Prop :=
  ∀ n a : ℕ, 11 ≤ n → n ≤ 13 → a ≤ 4 →
    ∀ G : SimpleGraph (Fin n),
      missingEdgeCount G = n - 4 + a →
        HasStrongFractionalPacking G (a : ℝ)

/-- The checked exact certificate families at orders `7`--`10` complete any
strong certificate family at orders `11`--`13` to the full companion-paper
base proposition. -/
theorem almostCompleteCertificateBases_of_strong
    (hstrong : AlmostCompleteStrongCertificateBases) :
    AlmostCompleteCertificateBases :=
  ⟨hstrong, CertificateExhaustion.exactCertificateBases⟩

/-- The strong theorem and the checked exact small bases imply the exact
almost-complete fractional-decomposition theorem. -/
theorem almostCompleteFractionalDecomposition_of_strong
    (hbases : AlmostCompleteCertificateBases)
    (hstrong : AlmostCompleteStrong) :
    AlmostCompleteFractionalDecomposition := by
  intro n hn G hmissing
  by_cases hn10 : n ≤ 10
  · apply fractionalDecomposition_of_exact_missing
      (A := Fin n) (by simpa) (m := n - 4) (by simp)
      (hbases.2 n hn hn10) G hmissing
  · have hn11 : 11 ≤ n := by omega
    obtain ⟨w, hw, hunc, _⟩ := hstrong n 0 hn11 (by omega) G (by simpa using hmissing)
    refine ⟨w, (isFractionalDecomposition_iff hw).2 ?_⟩
    exact le_antisymm (by simpa using hunc) (fractionalUncoveredWeight_nonneg hw)

/-- Fully assembled companion theorem from its remaining finite strong
certificate input.  The exact bases at orders `7`--`10` and the complete
structural step D5--D8 are unconditional and therefore absent from this
interface. -/
theorem almostCompleteFractionalDecomposition_of_components
    (hbases : AlmostCompleteStrongCertificateBases) :
    AlmostCompleteFractionalDecomposition := by
  let hall := almostCompleteCertificateBases_of_strong hbases
  exact almostCompleteFractionalDecomposition_of_strong hall
    (almostCompleteStrong_of_certificateBases_and_structuralStep hall
      almostCompleteStructuralStep)

end

end Erdos76
