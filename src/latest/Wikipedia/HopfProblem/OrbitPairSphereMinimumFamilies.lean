import Wikipedia.HopfProblem.OrbitPairSphereMinimumDeformation

/-!
# Deformation to a continuous family of actual semicircles

The minimum endpoint is expressed using a genuine continuous family of unit
tangent directions, via the explicit minimum-locus homeomorphism. Those same
directions define a jointly continuous family of sphere paths with the literal
antipodal endpoints. Comparison with arbitrary continuous paths remains separate.
-/

noncomputable section

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereSemicircle

variable {M : Type*} [TopologicalSpace M] {n m : ℕ}

def semicircleFamilyVertices (a : Sphere n) (τ : Fin (m + 2) → ℝ)
    (Y : C(M, Direction a)) : C(M, Space n m) :=
  ⟨fun x => semicircleVertices a τ (Y x), (continuous_semicircleVertices a τ).comp Y.continuous⟩

def semicirclePathFamily (a : Sphere n) (Y : C(M, Direction a)) :
    C(unitInterval × M, Sphere n) where
  toFun p := ⟨SphereGreatCircle.curve a.val (Y p.2).val Real.pi p.1, by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      SphereGreatCircle.norm_curve (ClosedHemisphere.unit_norm a) (Y p.2).2.1 (Y p.2).2.2
        Real.pi p.1⟩
  continuous_toFun := by
    have ht : Continuous (fun p : unitInterval × M => Real.pi * (p.1 : ℝ)) :=
      (continuous_subtype_val.comp continuous_fst).const_mul Real.pi
    have hy : Continuous (fun p : unitInterval × M => (Y p.2).val) :=
      continuous_subtype_val.comp (Y.continuous.comp continuous_snd)
    have hc : Continuous (fun p : unitInterval × M =>
        SphereGreatCircle.curve a.val (Y p.2).val Real.pi p.1) :=
      ((Real.continuous_cos.comp ht).smul continuous_const).add
        ((Real.continuous_sin.comp ht).smul hy)
    exact hc.subtype_mk _

theorem semicirclePathFamily_zero (a : Sphere n) (Y : C(M, Direction a)) (x : M) :
    semicirclePathFamily a Y (0, x) = a := by
  apply Subtype.ext
  exact SphereGreatCircle.curve_zero a.val (Y x).val Real.pi

theorem semicirclePathFamily_one (a b : Sphere n) (hanti : b.val = -a.val)
    (Y : C(M, Direction a)) (x : M) : semicirclePathFamily a Y (1, x) = b := by
  apply Subtype.ext
  exact (SphereGreatCircle.curve_pi_one a.val (Y x).val).trans hanti.symm

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem exists_homotopy_to_direction_family (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (cap : ℝ) (hcap : Real.pi ^ 2 < cap)
    (hmesh : ∀ i : Fin (m + 1), cap * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (j : Fin m) (hd : finrank ℝ B + 2 < 2 * n)
    (p : C(M, Space n m)) (start : ℝ) (hstart : start < cap)
    (hpstart : ∀ x, energy a b τ (p x) ≤ start) :
    ∃ Y : C(M, Direction a),
      ∃ G : ContinuousMap.HomotopyRel p (semicircleFamilyVertices a τ Y)
          (p ⁻¹' minimumSet a b τ),
        ∀ t x, G (t, x) ∈ energySublevel a b τ cap := by
  obtain ⟨q, hq, G, hG⟩ := exists_homotopy_into_minimum (I := I)
    a b τ hτ hzero hone hanti cap hcap hmesh j hd p start hstart hpstart
  let qm : C(M, minimumSet a b τ) := ⟨fun x => ⟨q x, hq x⟩, q.continuous.subtype_mk _⟩
  let e := directionMinimumHomeomorph a b τ hτ hzero hone hanti
    (minimum_mesh_of_cap τ hτ cap hcap.le hmesh) j
  let Y : C(M, Direction a) :=
    ⟨fun x => e.symm (qm x), e.symm.continuous.comp qm.continuous⟩
  have hend : semicircleFamilyVertices a τ Y = q := by
    apply ContinuousMap.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply (qm x))
  exact ⟨Y, G.cast rfl hend.symm, hG⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
