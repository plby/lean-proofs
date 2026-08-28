import Wikipedia.NoExoticSixSphere.OrthogonalPolygonRealization
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Polygon vertices are coordinates on the realized path family

Sampling the interior subdivision times recovers every vertex exactly.
The jointly continuous realization therefore gives a homeomorphism from
the admissible vertex space onto its image in the actual continuous path
space, with the compact-open topology.
-/

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

noncomputable def realization (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) :
    C(admissible a b m, C(ℝ, OrthogonalOperators n)) := (family a b τ).curry

noncomputable def sample (τ : Fin (m + 2) → ℝ) (P : C(ℝ, OrthogonalOperators n)) : Space n m :=
  fun i ↦ P (τ i.castSucc.succ)

theorem continuous_sample (τ : Fin (m + 2) → ℝ) :
    Continuous (sample (n := n) τ) := by
  apply continuous_pi
  intro i
  exact continuous_eval_const _

theorem sample_realization (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible a b m) : sample τ (realization a b τ v) = v.1 := by
  funext i
  change path a b τ v.1 (τ i.castSucc.succ) = v.1 i
  rw [path_vertex a b τ hτ v.2, vertices_interior]

noncomputable def recoveredVertices (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (P : Set.range (realization a b τ)) : admissible a b m :=
  ⟨sample τ P.1, by
    obtain ⟨v, hv⟩ := P.2
    rw [← hv, sample_realization a b τ hτ v]
    exact v.2⟩

theorem recovered_realization (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : admissible a b m) :
    recoveredVertices a b τ hτ ⟨realization a b τ v, ⟨v, rfl⟩⟩ = v :=
  Subtype.ext (sample_realization a b τ hτ v)

theorem realization_recovered (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (P : Set.range (realization a b τ)) :
    realization a b τ (recoveredVertices a b τ hτ P) = P.1 := by
  rcases P with ⟨P, v, rfl⟩
  rw [recovered_realization]

noncomputable def realizationHomeomorph (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) : (admissible a b m) ≃ₜ Set.range (realization a b τ) where
  toFun v := ⟨realization a b τ v, ⟨v, rfl⟩⟩
  invFun := recoveredVertices a b τ hτ
  left_inv := recovered_realization a b τ hτ
  right_inv P := Subtype.ext (realization_recovered a b τ hτ P)
  continuous_toFun := (realization a b τ).continuous.subtype_mk _
  continuous_invFun := ((continuous_sample τ).comp continuous_subtype_val).subtype_mk _

end NoExoticSixSphere.OrthogonalPolygon
