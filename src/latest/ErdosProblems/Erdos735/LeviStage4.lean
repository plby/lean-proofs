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

import ErdosProblems.Erdos735.LeviSignVector
import ErdosProblems.Erdos735.Discharging4

/-!
# The Levi-to-Stage-4 bridge

This file isolates the geometric extraction required of the concrete blue
cellulation: a Hall violation in its helping graph determines an arrangement
line for which the only incident triangles are the two endpoint triangles.
-/

namespace Erdos735
namespace ABKPR
namespace HelpingGraph

open SignVectorArrangement
open SignVector

universe uH uE

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {Help : Type uH} {Evil : Type uE}
variable [Fintype Help] [Fintype Evil] [DecidableEq Help] [DecidableEq Evil]

/-- The exact path-to-selected-line extraction furnished by the concrete
blue cellulation. -/
structure LeviPathBridge (G : HelpingGraph Help Evil) (n : I → Vec3) where
  certificate : ¬ G.NoEvilEvilPath → EvilPathLineCertificate n

/-- Sign-vector Levi excludes evil--evil paths, hence produces the Hall
hypothesis used by `exists_adjacent_matching`. -/
theorem noEvilEvilPath_of_signVectorLevi
    {G : HelpingGraph Help Evil} {n : I → Vec3}
    (H : HasSignVectorLeviProperty n) (B : LeviPathBridge G n) :
    G.NoEvilEvilPath := by
  by_contra hpath
  exact no_evil_path_of_levi_certificate H (B.certificate hpath)

/-- Antipodally correct path bridge: its two projective endpoint triangles
cover four strict spherical faces. -/
structure ProjectiveLeviPathBridge (G : HelpingGraph Help Evil)
    (n : I → Vec3) where
  certificate : ¬ G.NoEvilEvilPath → ProjectiveEvilPathLineCertificate n

/-- The strengthened six-strict-face form of Levi excludes a path whose
incident triangles lie in two antipodal endpoint orbits. -/
theorem noEvilEvilPath_of_projective_signVectorLevi
    {G : HelpingGraph Help Evil} {n : I → Vec3}
    (H : HasProjectiveSignVectorLeviProperty n)
    (B : ProjectiveLeviPathBridge G n) : G.NoEvilEvilPath := by
  by_contra hpath
  exact no_evil_path_of_projective_levi_certificate H (B.certificate hpath)

end HelpingGraph
end ABKPR
end Erdos735
