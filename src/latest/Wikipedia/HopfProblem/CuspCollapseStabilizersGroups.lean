import Wikipedia.HopfProblem.CuspCollapseFibreTorus
import Wikipedia.HopfProblem.CuspCollapseStabilizersBasic
import Wikipedia.HopfProblem.CuspCollapseStabilizers

/-!
# The compact subgroups appearing as central-fibre stabilizers

The subgroup attached to an edge direction is the image of its explicit
circle of integral powers.  These are subgroups of the actual compact
fibre torus acting on the original toric gluing.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

/-- The circle homomorphism associated to an integral edge direction. -/
def edgeCompactPhase (d : Fin 2 → ℤ) : Circle →* CompactFibreTorus where
  toFun a i := a ^ d i
  map_one' := by
    funext i
    exact one_zpow (d i)
  map_mul' a b := by
    funext i
    exact mul_zpow a b (d i)

@[simp] theorem edgeCompactPhase_apply (d : Fin 2 → ℤ) (a : Circle) (i : Fin 2) :
    edgeCompactPhase d a i = a ^ d i := rfl

/-- The explicit phase circle for two vertices of one actual triangle. -/
abbrev edgePhase (s : Triangle) (j k : Fin 3) : Circle →* CompactFibreTorus :=
  edgeCompactPhase (s.vertex k - s.vertex j)

@[simp] theorem edgePhase_apply (s : Triangle) (j k : Fin 3) (a : Circle) (i : Fin 2) :
    edgePhase s j k a i = a ^ (s.vertex k i - s.vertex j i) := rfl

/-- The edge-circle subgroup inside the actual compact fibre torus. -/
def edgeCircle (d : Fin 2 → ℤ) : Subgroup CompactFibreTorus := (edgeCompactPhase d).range

theorem mem_edgeCircle_iff (d : Fin 2 → ℤ) (u : CompactFibreTorus) :
    u ∈ edgeCircle d ↔ ∃ a : Circle, ∀ i : Fin 2, u i = a ^ d i := by
  change (∃ a : Circle, edgeCompactPhase d a = u) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i => (congrFun ha i).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun i => (ha i).symm⟩

/-- Reversing an edge reverses its parametrization but not its circle subgroup. -/
@[simp] theorem edgeCircle_neg (d : Fin 2 → ℤ) : edgeCircle (-d) = edgeCircle d := by
  ext u
  rw [mem_edgeCircle_iff, mem_edgeCircle_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a⁻¹, fun i => ?_⟩
    simpa only [Pi.neg_apply, zpow_neg, inv_zpow] using ha i
  · rintro ⟨a, ha⟩
    refine ⟨a⁻¹, fun i => ?_⟩
    simpa only [Pi.neg_apply, zpow_neg, inv_zpow, inv_inv] using ha i

theorem edgeCompactPhase_continuous (d : Fin 2 → ℤ) :
    Continuous (edgeCompactPhase d) := by
  apply continuous_pi
  intro i
  exact continuous_id.zpow (d i)

theorem edgeCircle_isCompact (d : Fin 2 → ℤ) :
    IsCompact (edgeCircle d : Set CompactFibreTorus) :=
  isCompact_range (edgeCompactPhase_continuous d)

/-- An actual triangle edge gives an injectively parametrized circle,
not an arbitrary possibly nonprimitive lattice image. -/
theorem edgeCompactPhase_vertex_injective (s : Triangle) (j k : Fin 3) (hjk : j ≠ k) :
    Function.Injective (edgeCompactPhase (s.vertex k - s.vertex j)) :=
  vertexDifferencePhase_injective s j k hjk

theorem edgePhase_injective (s : Triangle) (j k : Fin 3) (hjk : j ≠ k) :
    Function.Injective (edgePhase s j k) := edgeCompactPhase_vertex_injective s j k hjk

/-- The edge stabilizer has the usual circle topology inherited from the
compact fibre torus. -/
def edgeCircleHomeomorph (s : Triangle) (j k : Fin 3) (hjk : j ≠ k) :
    Circle ≃ₜ edgeCircle (s.vertex k - s.vertex j) :=
  ((edgeCompactPhase_continuous (s.vertex k - s.vertex j)).isClosedEmbedding
    (edgeCompactPhase_vertex_injective s j k hjk)).toIsEmbedding.toHomeomorph

@[simp] theorem edgeCircleHomeomorph_coe (s : Triangle) (j k : Fin 3) (hjk : j ≠ k)
    (a : Circle) :
    (edgeCircleHomeomorph s j k hjk a : CompactFibreTorus) =
      edgeCompactPhase (s.vertex k - s.vertex j) a := rfl

/-- The stabilizer subgroup is trivial on the open central component
stratum, and also on the dense noncentral torus. -/
theorem compactFibre_stabilizer_eq_bot_of_at_most_one_zero
    (s : Triangle) (z : CoordinateSpace 3) (j : Fin 3)
    (hz : ∀ i, i ≠ j → z i ≠ 0) :
    MulAction.stabilizer CompactFibreTorus (inclusion s z) = ⊥ := by
  ext u
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  exact compactFibreAction_inclusion_eq_self_iff_of_at_most_one_zero u s z j hz

/-- The stabilizer subgroup on an open double curve is precisely the
embedded circle with its vertex-difference direction. -/
theorem compactFibre_stabilizer_eq_edgeCircle_of_two_zero
    (s : Triangle) (z : CoordinateSpace 3) (j k : Fin 3) (hjk : j ≠ k)
    (hzj : z j = 0) (hzk : z k = 0)
    (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) :
    MulAction.stabilizer CompactFibreTorus (inclusion s z) =
      edgeCircle (s.vertex k - s.vertex j) := by
  ext u
  rw [MulAction.mem_stabilizer_iff, mem_edgeCircle_iff]
  exact compactFibreAction_inclusion_eq_self_iff_of_two_zero u s z j k hjk hzj hzk hz

/-- The stabilizer on an actual open double curve is homeomorphic to the
ordinary circle with its usual topology. -/
def compactFibreStabilizerCircleHomeomorph
    (s : Triangle) (z : CoordinateSpace 3) (j k : Fin 3) (hjk : j ≠ k)
    (hzj : z j = 0) (hzk : z k = 0)
    (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) :
    Circle ≃ₜ MulAction.stabilizer CompactFibreTorus (inclusion s z) :=
  (edgeCircleHomeomorph s j k hjk).trans (Homeomorph.setCongr (by
    rw [compactFibre_stabilizer_eq_edgeCircle_of_two_zero s z j k hjk hzj hzk hz]))

@[simp] theorem compactFibreStabilizerCircleHomeomorph_coe
    (s : Triangle) (z : CoordinateSpace 3) (j k : Fin 3) (hjk : j ≠ k)
    (hzj : z j = 0) (hzk : z k = 0)
    (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) (a : Circle) :
    (compactFibreStabilizerCircleHomeomorph s z j k hjk hzj hzk hz a : CompactFibreTorus) =
      edgePhase s j k a := rfl

/-- At a triple intersection the stabilizer is the full compact fibre torus. -/
theorem compactFibre_stabilizer_inclusion_zero (s : Triangle) :
    MulAction.stabilizer CompactFibreTorus (inclusion s 0) = ⊤ := by
  ext u
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun _ => Subgroup.mem_top u, fun _ => compactFibreAction_inclusion_zero u s⟩

end Wikipedia.HopfProblem.ToricSpace
