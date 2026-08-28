import Wikipedia.HopfProblem.CuspCentralFibre
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.LocallyContractible

/-!
# Contractible neighbourhoods in the actual normal-crossing affine fibre

Near a point of `z₀ z₁ z₂ = 0`, every coordinate which is nonzero at the
centre remains nonzero.  Consequently every nearby zero-product point
lies on a coordinate plane containing that centre.  A sufficiently
small relative ball is therefore star-convex about its actual centre.
The contractions retain the original affine subspace topology.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspLocallyContractible

open ToricCharts ToricFan CuspQuotient

local notation "E₃" => CoordinateSpace 3

/-- Exclude the coordinate planes which do not contain the specified centre. -/
def activeNeighborhood (a : E₃) : Set E₃ :=
  {z | ∀ j : Fin 3, a j ≠ 0 → z j ≠ 0}

theorem activeNeighborhood_isOpen (a : E₃) : IsOpen (activeNeighborhood a) := by
  have he : activeNeighborhood a = ⋂ j : Fin 3, {z : E₃ | a j ≠ 0 → z j ≠ 0} := by
    ext z
    simp [activeNeighborhood]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  by_cases hj : a j = 0
  · simp [hj]
  · have h : IsOpen {z : E₃ | z j ≠ 0} :=
      isOpen_ne_fun (continuous_apply j) continuous_const
    have he : {z : E₃ | a j ≠ 0 → z j ≠ 0} = {z : E₃ | z j ≠ 0} := by
      ext z
      exact ⟨fun hz => hz hj, fun hz _ => hz⟩
    rw [he]
    exact h

theorem self_mem_activeNeighborhood (a : E₃) : a ∈ activeNeighborhood a := fun _ h => h

theorem centralAffine_exists_zero (z : E₃) (hz : z ∈ centralAffine) :
    ∃ j : Fin 3, z j = 0 := by
  obtain h | h | h := (Triangle.central_fibre z).mp hz
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem mem_centralAffine_of_coordinate_eq_zero (z : E₃) (j : Fin 3) (hj : z j = 0) :
    z ∈ centralAffine := by
  have hprod : (∏ i : Fin 3, z i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
  simpa [centralAffine, Triangle.time, Fin.prod_univ_succ, mul_assoc] using hprod

/-- The actual small affine fibre ball contracts linearly to its actual centre. -/
theorem centralBall_starConvex (a : centralAffine) (r : ℝ) (hr : 0 < r)
    (hactive : Metric.ball a.val r ⊆ activeNeighborhood a.val) :
    StarConvex ℝ a.val (centralAffine ∩ Metric.ball a.val r) := by
  intro z hz u v hu hv huv
  refine ⟨?_, (convex_ball a.val r).starConvex (Metric.mem_ball_self hr) hz.2 hu hv huv⟩
  obtain ⟨j, hj⟩ := centralAffine_exists_zero z hz.1
  have ha : a.val j = 0 := by
    by_contra ha
    exact (hactive hz.2 j ha) hj
  apply mem_centralAffine_of_coordinate_eq_zero _ j
  simp [Pi.add_apply, Pi.smul_apply, ha, hj]

/-- Relative metric balls are the literal affine fibre intersected with ambient metric balls. -/
def centralBallHomeomorph (a : centralAffine) (r : ℝ) :
    Metric.ball a r ≃ₜ ↥(centralAffine ∩ Metric.ball a.val r) where
  toFun z := ⟨z.val.val, z.val.property, z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _ |>.subtype_mk _

/-- A sufficiently small actual relative ball is contractible in its own original topology. -/
theorem centralBall_contractible (a : centralAffine) (r : ℝ) (hr : 0 < r)
    (hactive : Metric.ball a.val r ⊆ activeNeighborhood a.val) :
    ContractibleSpace (Metric.ball a r) :=
  (centralBallHomeomorph a r).contractibleSpace_iff.mpr
    ((centralBall_starConvex a r hr hactive).contractibleSpace
      ⟨a.val, a.property, Metric.mem_ball_self hr⟩)

/-- Contractible neighbourhoods form a basis in the original affine normal-crossing fibre. -/
instance centralAffine_stronglyLocallyContractible :
    StronglyLocallyContractibleSpace centralAffine where
  contractible_basis a := by
    rw [hasBasis_self]
    intro U hU
    obtain ⟨r, hr, hactive⟩ := Metric.mem_nhds_iff.mp
      ((activeNeighborhood_isOpen a.val).mem_nhds (self_mem_activeNeighborhood a.val))
    obtain ⟨s, hs, hUball⟩ := Metric.mem_nhds_iff.mp hU
    have ht : 0 < min r s := lt_min hr hs
    refine ⟨Metric.ball a (min r s), Metric.ball_mem_nhds a ht, ?_, ?_⟩
    · exact centralBall_contractible a (min r s) ht
        ((Metric.ball_subset_ball (min_le_left r s)).trans hactive)
    · exact (Metric.ball_subset_ball (min_le_right r s)).trans hUball

/-- The original affine normal-crossing fibre also satisfies Mathlib's weaker classical notion. -/
theorem centralAffine_locallyContractible : LocallyContractibleSpace centralAffine :=
  StronglyLocallyContractibleSpace.locallyContractible

end Wikipedia.HopfProblem.CuspLocallyContractible
