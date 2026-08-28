import Wikipedia.NoExoticSixSphere.OrthogonalPolygon

/-!
# The open domain of strictly short polygons

Strict shortness persists under small changes of the vertices. The topology
is the original product topology, and the logarithms are used only on their
actual open chart domain.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

def shortDomain (a b : OrthogonalOperators n) (m : ℕ) : Set (Space n m) :=
  {v | v ∈ admissible a b m ∧ ∀ i, ‖generator a b v i‖ < Real.pi}

theorem shortDomain_mem_nhds (a b : OrthogonalOperators n) {v : Space n m}
    (hv : v ∈ shortDomain a b m) : shortDomain a b m ∈ 𝓝 v := by
  have hU := (isOpen_admissible a b m).mem_nhds hv.1
  have hnorm (i : Fin (m + 1)) : ∀ᶠ w in 𝓝 v, ‖generator a b w i‖ < Real.pi :=
    ((contMDiffOn_generator a b i).contMDiffAt hU).continuousAt.norm.eventually
      (gt_mem_nhds (hv.2 i))
  filter_upwards [hU, eventually_all.mpr hnorm] with w hw hn
  exact ⟨hw, hn⟩

theorem isOpen_shortDomain (a b : OrthogonalOperators n) (m : ℕ) : IsOpen (shortDomain a b m) :=
  isOpen_iff_mem_nhds.mpr (fun _ hv ↦ shortDomain_mem_nhds a b hv)

end NoExoticSixSphere.OrthogonalPolygon
