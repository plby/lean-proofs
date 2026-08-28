import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumDeformation

/-!
# Deformation to continuous families of balanced rotations

The minimum-locus homeomorphism recovers a continuous family of actual
balanced real involutions from the endpoint of the polygon deformation.
-/

open Set Module
open scoped Matrix.Norms.Frobenius ContDiff Manifold Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices

variable {M : Type*} [TopologicalSpace M] {n m : ℕ}

noncomputable def rotationFamilyVertices (τ : Fin (m + 2) → ℝ)
    (P : C(M, BalancedRealInvolutions.Space n)) : C(M, VertexSpace.Space (Index n) m) :=
  ⟨fun x ↦ rotationVertices τ (P x), (continuous_rotationVertices n τ).comp P.continuous⟩

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]

include I

theorem exists_homotopy_to_rotation_family (n : ℕ)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hsmall : ∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))
    (cap : ℝ) (hcap : (4 * n : ℝ) * Real.pi ^ 2 < cap)
    (hcompact : IsCompact (energySublevel specialIdentity (antipode n) τ cap))
    (hd : finrank ℝ B < n)
    (p : C(M, VertexSpace.Space (Index n) m))
    (hp : ∀ x, p x ∈ admissible specialIdentity (antipode n) m)
    (start : ℝ) (hstart : start < cap)
    (hpstart : ∀ x, energy specialIdentity (antipode n) τ (p x) ≤ start) :
    ∃ P : C(M, BalancedRealInvolutions.Space n),
      ∃ G : ContinuousMap.HomotopyRel p (rotationFamilyVertices τ P)
        (p ⁻¹' minimumSet n τ),
        ∀ t x, G (t, x) ∈ energySublevel specialIdentity (antipode n) τ cap := by
  obtain ⟨q, hq, G, hG⟩ := exists_homotopy_into_minimum (I := I)
    n τ hτ hzero hone hsmall cap hcap hcompact hd p hp start hstart hpstart
  let qm : C(M, minimumSet n τ) := ⟨fun x ↦ ⟨q x, hq x⟩, q.continuous.subtype_mk _⟩
  let e := rotationMinimumHomeomorph n τ hτ hzero hone hsmall
    (isCompact_energySublevel_of_le specialIdentity (antipode n) τ hcap.le hcompact)
  let P : C(M, BalancedRealInvolutions.Space n) :=
    ⟨fun x ↦ e.symm (qm x), e.symm.continuous.comp qm.continuous⟩
  have hend : rotationFamilyVertices τ P = q := by
    apply ContinuousMap.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply (qm x))
  exact ⟨P, G.cast rfl hend.symm, hG⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
