import Wikipedia.NoExoticSixSphere.OpenMapHomotopyExtension
import Wikipedia.NoExoticSixSphere.SphereFiberGermHomotopy
import Mathlib.Topology.UrysohnsLemma

/-!
# From a fiber-preserving local homotopy to a global sphere-map homotopy

On a compact Hausdorff source, a local homotopy near the distinguished
fiber is extended with a supported clock. The clock equals one on an
open neighborhood of the fiber, so the endpoint has the other map's
actual germ. The previously proved fiber-germ comparison finishes the
global homotopy. Preservation of the distinguished fiber is proved at
the intermediate endpoint, not postulated.
-/

noncomputable section

open Set Filter Topology
open scoped unitInterval

namespace NoExoticSixSphere.SphereFiberGerm

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}

theorem homotopic_of_local_fiber_homotopy (f g : C(X, Sphere n)) (b : Sphere n)
    (hK : ∀ x, f x = b ↔ g x = b) (U : Set X) (hU : IsOpen U)
    (hKU : f ⁻¹' {b} ⊆ U) (L : C(I × U, Sphere n))
    (hzero : ∀ x : U, L (0, x) = f x.val)
    (hone : ∀ x : U, L (1, x) = g x.val)
    (hfiber : ∀ (t : I) (x : U), L (t, x) = b ↔ f x.val = b) :
    f.Homotopic g := by
  have hclosed : IsClosed (f ⁻¹' {b}) := isClosed_singleton.preimage f.continuous
  obtain ⟨V, hV, hKV, hVU⟩ := normal_exists_closure_subset hclosed hU hKU
  obtain ⟨β, hβsupport, hβone, hβbound⟩ := exists_tsupport_one_of_isOpen_isClosed hU
    isClosed_closure.isCompact isClosed_closure hVU
  let p := OpenMapHomotopyExtension.endpoint f L β hβbound hzero hU hβsupport
  let H := OpenMapHomotopyExtension.homotopy f L β hβbound hzero hU hβsupport
  have hp : ∀ x, p x = b ↔ f x = b := by
    intro x
    change OpenMapHomotopyExtension.raw f L β hβbound (1, x) = b ↔ f x = b
    by_cases hx : x ∈ U
    · rw [OpenMapHomotopyExtension.raw_of_mem f L β hβbound hx]
      exact hfiber _ ⟨x, hx⟩
    · rw [OpenMapHomotopyExtension.raw_of_notMem f L β hβbound hx]
  have hgerm : ∀ x, p x = b → (p : X → Sphere n) =ᶠ[𝓝 x] g := by
    intro x hx
    filter_upwards [hV.mem_nhds (hKV ((hp x).mp hx))] with y hy
    exact (OpenMapHomotopyExtension.endpoint_of_one f L β hβbound hzero hU hβsupport
      (hVU (subset_closure hy)) (hβone (subset_closure hy))).trans (hone _)
  obtain ⟨H', -⟩ := exists_homotopy_of_fiber_germs p g b
    (fun x ↦ (hp x).trans (hK x)) hgerm
  exact ⟨H.trans H'⟩

end NoExoticSixSphere.SphereFiberGerm
