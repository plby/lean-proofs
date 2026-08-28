import Wikipedia.NoExoticSixSphere.FrameBoundaryInterpolation
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!
# Installing frame data on a whole thin product near a compact zero section

Frame interpolation preserves projected injectivity on the original compact
product. A uniform transverse radius turns agreement near the protected zero
section into agreement on an entire smaller closed product over that set.
-/

noncomputable section

open Set Metric Function Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

theorem exists_frameInterpolation_product {N n d : ℕ} {K S : Set (Vector 4)}
    (hK : IsCompact K) (hS : IsCompact S) (r : ℝ) (hr : 0 < r)
    (A F : C(Vector 4 × Vector d, Vector n →L[ℝ] Vector N))
    (P : Vector 4 × Vector d → Vector N →L[ℝ] Vector N)
    (hP : ContinuousOn P (K ×ˢ closedBall (0 : Vector d) r))
    (hA : ∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, Injective ((P p).comp (A p)))
    (heq : ∀ x ∈ S, F (x, 0) = A (x, 0)) :
    ∃ B : C(Vector 4 × Vector d, Vector n →L[ℝ] Vector N),
      (∀ p ∈ K ×ˢ closedBall (0 : Vector d) r, Injective ((P p).comp (B p))) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ r ∧ ∃ U : Set (Vector 4 × Vector d), IsOpen U ∧
        S ×ˢ closedBall (0 : Vector d) ε ⊆ U ∧ EqOn B F U := by
  have heq' : EqOn F A (S ×ˢ ({0} : Set (Vector d))) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact heq x hx
  obtain ⟨B, hBi, U, hU, hSU, hBF⟩ := exists_boundaryInterpolation
    (hK.prod (isCompact_closedBall (0 : Vector d) r)) (hS.prod isCompact_singleton)
    A F P hP hA heq'
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let q : S × Vector d → Vector 4 × Vector d := fun p ↦ (p.1.val, p.2)
  have hq : Continuous q :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  obtain ⟨δ, hδ, hδU⟩ := exists_uniform_closedProductTube (hU.preimage hq)
    (fun x ↦ hSU ⟨x.property, rfl⟩)
  refine ⟨B, hBi, min δ r, lt_min hδ hr, min_le_right _ _, U, hU, ?_, hBF⟩
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  apply hδU ⟨x, hx⟩ v
  have hvr := (closedBall_subset_closedBall (min_le_left δ r)) hv
  simpa only [mem_closedBall, dist_zero_right] using hvr

end NoExoticSixSphere.Stiefel
