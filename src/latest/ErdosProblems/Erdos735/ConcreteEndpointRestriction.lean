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
-/

import ErdosProblems.Erdos735.RedChordEndpointRestriction
import ErdosProblems.Erdos735.Discharging12

/-!
# Concrete ABKPR endpoint restriction

This is the final interface bridge from the projective red-sector theorem to
`ABKPR.Data.EndpointRestriction`.  A data constructor whose across pairing and red-endpoint
finsets are those extracted from the rotation realization satisfies its endpoint restriction.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace Erdos735.RedChordExtraction.Geometry

open ProjectiveArrangement SignVector
open SignVector.RotationRealization

variable {A B : Finset Point}
variable {G : SimpleGraph (BlueVertex B)} [DecidableRel G.Adj] [Fintype G.edgeSet]
variable (X : RotationRealization (G := G) (blueNormals B) (blueNormals_ne_zero B))
variable (H : Geometry (A := A) (B := B) X)
variable (D : ABKPR.Data X.strictC)

/-- Transport the concrete red-sector endpoint exclusion into the exact
`ABKPR.Data.EndpointRestriction` interface.  The two compatibility equalities
are definitional for the data constructor built from `X` and `H`. -/
theorem toABKPREndpointRestriction
    (hacross : ∀ d, D.across d = X.across d)
    (hendpoints : ∀ f,
      D.redEndpoints f = redEndpoints (A := A) (B := B) X H f) :
    D.EndpointRestriction := by
  intro f i hbad
  have hallD : D.redEndpoints (D.across ⟨f, i⟩).1 = Finset.univ :=
    D.redEndpoints_eq_univ_of_twoDiagonal hbad.1
  have hallX : redEndpoints (A := A) (B := B) X H (X.across ⟨f, i⟩).1 =
      Finset.univ := by
    rw [← hendpoints]
    rw [← congrArg Sigma.fst (hacross ⟨f, i⟩)]
    exact hallD
  have hres := endpointRestriction_of_across_all_red
    (A := A) (B := B) X H f i hallX
  constructor
  · rw [hendpoints]
    exact hres.1
  · have hsucc : ABKPR.faceSucc X.strictC f i = X.strictFaceSucc f i := by
      apply Fin.ext
      rfl
    rw [hendpoints f, hsucc]
    exact hres.2

end Erdos735.RedChordExtraction.Geometry
