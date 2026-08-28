import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundary

/-!
# The punctured closed new face, including the common corner

The inverse of the original closed radial exchange maps this entire piece
into the original attaching-core complement. Its boundary-quotient map
agrees with the new open patch wherever the latter is defined.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

def oldClosedOverlap : C(UnitSphere E × PuncturedBall F, oldPatch A) :=
  ⟨fun z => ⟨A.map (z.1, ⟨z.2.val, mem_closedBall_zero_iff.mpr z.2.property.2⟩),
    fun h => z.2.property.1 ((face_mem_core_iff A _ _).mp h)⟩,
    (A.map.continuous.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _))).subtype_mk _⟩

theorem oldClosedOverlap_open (z : Overlap E F) :
    oldClosedOverlap A (z.1, ⟨z.2.val, z.2.property.1, z.2.property.2.le⟩) = oldOverlap A z := rfl

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def newOuterMap : C(PuncturedBall E × UnitSphere F, Boundary A n) :=
  ((oldMap A n).comp (oldClosedOverlap A)).comp
    ⟨(exchange E F).symm, (exchange E F).symm.continuous⟩

theorem newOuterMap_exchange (z : UnitSphere E × PuncturedBall F) :
    newOuterMap A n (exchange E F z) = oldMap A n (oldClosedOverlap A z) := by
  change oldMap A n (oldClosedOverlap A ((exchange E F).symm (exchange E F z))) = _
  rw [Homeomorph.symm_apply_apply]

omit [FiniteDimensional ℝ E] in
theorem exchange_open_closed (z : Overlap E F) :
    exchange E F (z.1, ⟨z.2.val, z.2.property.1, z.2.property.2.le⟩) =
      (⟨(openExchange m n z).1.val, (openExchange m n z).1.property.1,
        (openExchange m n z).1.property.2.le⟩, (openExchange m n z).2) := by
  exact Prod.ext (Subtype.ext rfl) rfl

theorem newOuterMap_open (u : openPuncturedDisk E) (v : UnitSphere F) :
    newOuterMap A n (⟨u.val, u.property.1, u.property.2.le⟩, v) =
      newMap A n (⟨u.val, mem_ball_zero_iff.mpr u.property.2⟩, v) := by
  let z := (openExchange m n).symm (u, v)
  have he := exchange_open_closed (m := m) n z
  have hz : openExchange m n z = (u, v) := (openExchange m n).apply_symm_apply (u, v)
  rw [hz] at he
  rw [← he, newOuterMap_exchange, oldClosedOverlap_open, overlap_identification]
  exact congrArg (fun p : openPuncturedDisk E × UnitSphere F =>
    newMap A n ((⟨p.1.val, mem_ball_zero_iff.mpr p.1.property.2⟩ : openUnitDisk E), p.2)) hz

theorem newOuterMap_corner (u : UnitSphere E) (v : UnitSphere F) :
    newOuterMap A n (boundaryPoint u, v) =
      oldMap A n (oldClosedOverlap A (u, boundaryPoint v)) := by
  rw [← exchange_boundary u v]
  exact newOuterMap_exchange A n (u, boundaryPoint v)

end Wikipedia.SmoothSixDPoincare.FramedSurgery
