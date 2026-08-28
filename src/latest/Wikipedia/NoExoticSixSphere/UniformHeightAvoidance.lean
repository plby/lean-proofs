import Wikipedia.NoExoticSixSphere.StabilizedSpanningDisk
import Wikipedia.NoExoticSixSphere.UniformProductTube

/-!+# Uniform separation from a short cylinder over the entire old ambient space

A compact family disjoint from the old ambient space remains disjoint from
every sufficiently short height segment over that space. Compactness is
used only for the given family, not for any manifold in the old coordinates.
The added height and graph coordinates detect every possible intersection.
-/

noncomputable section

open Function Set

namespace NoExoticSixSphere.StabilizedSpanningDisk

theorem exists_uniform_height_avoidance {N : ℕ} {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (F : C(X, EuclideanSpace ℝ (Fin (N + 6))))
    (hF : ∀ x, F x ∉ range (appendZeroMap N 6)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x y t, ‖t‖ ≤ ε →
      F x ≠ coordinates N 4 ((y, t), 0) := by
  let L := coordinates N 4
  let extra : X → ℝ × (ℝ × EuclideanSpace ℝ (Fin 4)) :=
    fun x ↦ ((L.symm (F x)).1.2, (L.symm (F x)).2)
  have hP : Continuous (fun x ↦ L.symm (F x)) := L.symm.continuous.comp F.continuous
  have hE : Continuous extra := hP.fst.snd.prodMk hP.snd
  let U : Set (X × ℝ) := {p | extra p.1 ≠ (p.2, 0)}
  have hU : IsOpen U := isOpen_ne_fun (hE.comp continuous_fst)
    (continuous_snd.prodMk continuous_const)
  have hzero (x : X) : (x, (0 : ℝ)) ∈ U := by
    intro he
    have hheight := congrArg Prod.fst he
    have hgraph := congrArg Prod.snd he
    have hp : L.symm (F x) = (((L.symm (F x)).1.1, 0), 0) :=
      Prod.ext (Prod.ext rfl hheight) hgraph
    apply hF x
    refine ⟨(L.symm (F x)).1.1, ?_⟩
    calc
      appendZeroMap N 6 (L.symm (F x)).1.1 = L (((L.symm (F x)).1.1, 0), 0) :=
        (coordinates_old N 4 _).symm
      _ = L (L.symm (F x)) := congrArg L hp.symm
      _ = F x := L.apply_symm_apply _
  obtain ⟨ε, hε, hεU⟩ := exists_uniform_closedProductTube hU hzero
  refine ⟨ε, hε, ?_⟩
  intro x y t ht he
  apply hεU x t ht
  change ((L.symm (F x)).1.2, (L.symm (F x)).2) = (t, 0)
  rw [he]
  exact congrArg (fun p ↦ (p.1.2, p.2)) (L.symm_apply_apply ((y, t), 0))

end NoExoticSixSphere.StabilizedSpanningDisk
