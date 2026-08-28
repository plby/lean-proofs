import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometry

/-!
# Normal forms at every point of the literal global cusp fibre

The actual fibre homeomorphism supplies a native representative of every
point lying over infinity.  The ambient charts below use the unchanged
glued threefold atlas, and the coordinate factors count the actual local
branches of that fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms

open ToricCharts CuspGeometry

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace

/-- Every point of the literal sphere fibre at infinity has a centered
ambient normal-crossing chart with its actual number of branches. -/
theorem fibre_normalCrossingChart_with_branchCount (y : sphereCuspFibre) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      J.card = fibreBranchCount y ∧ J.Nonempty ∧
      (y : Threefold.Space) ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target,
        sphereChart (Threefold.projectionSphere (e.symm w)) = ∏ j ∈ J, w j := by
  obtain ⟨J, e, hcard, hJ, hys, hzero, hsource, hprod⟩ :=
    sphere_normalCrossingChart_with_branchCount
      (centralFibreHomeomorph.symm y : LocalSpace) (centralFibreHomeomorph.symm y).property
  rw [centralFibreHomeomorph_symm_inclusion] at hys hzero
  exact ⟨J, e, hcard, hJ, hys, hzero, hsource, hprod⟩

/-- The normal form stated directly for an ambient point whose actual
sphere projection is infinity. -/
theorem normalCrossingChart_at_sphereInfinity (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = (∞ : RiemannSphere)) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      J.card = fibreBranchCount ⟨y, hy⟩ ∧ J.Nonempty ∧
      y ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target,
        sphereChart (Threefold.projectionSphere (e.symm w)) = ∏ j ∈ J, w j :=
  fibre_normalCrossingChart_with_branchCount ⟨y, hy⟩

/-- The actual sphere projection has the single-coordinate form at
each point of the one-branch stratum of its literal cusp fibre. -/
theorem fibre_single_local_equation (y : sphereCuspFibre) (hy : fibreBranchCount y = 1) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      (y : Threefold.Space) ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 := by
  obtain ⟨e, hys, hzero, hsource, hprod⟩ :=
    sphere_single_local_equation (centralFibreHomeomorph.symm y : LocalSpace) hy
  rw [centralFibreHomeomorph_symm_inclusion] at hys hzero
  exact ⟨e, hys, hzero, hsource, hprod⟩

/-- The actual sphere projection has the two-coordinate product form
at each point of the two-branch stratum of its literal cusp fibre. -/
theorem fibre_double_local_equation (y : sphereCuspFibre) (hy : fibreBranchCount y = 2) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      (y : Threefold.Space) ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 * w 1 := by
  obtain ⟨e, hys, hzero, hsource, hprod⟩ :=
    sphere_double_local_equation (centralFibreHomeomorph.symm y : LocalSpace) hy
  rw [centralFibreHomeomorph_symm_inclusion] at hys hzero
  exact ⟨e, hys, hzero, hsource, hprod⟩

/-- The exact triple product holds at each actual triple point of the
literal global sphere fibre over infinity. -/
theorem fibre_triple_local_equation (y : sphereCuspFibre) (hy : fibreBranchCount y = 3) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      (y : Threefold.Space) ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target,
        sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 * w 1 * w 2 := by
  obtain ⟨e, hys, hzero, hsource, hprod⟩ :=
    sphere_triple_local_equation (centralFibreHomeomorph.symm y : LocalSpace) hy
  rw [centralFibreHomeomorph_symm_inclusion] at hys hzero
  exact ⟨e, hys, hzero, hsource, hprod⟩

/-- The three canonical equations exhaust every point of the actual
central fibre, with no hypothesis about the existence of normal forms. -/
theorem fibre_local_equation_one_two_three (y : sphereCuspFibre) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      (y : Threefold.Space) ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ((fibreBranchCount y = 1 ∧ ∀ w ∈ e.target,
          sphereChart (Threefold.projectionSphere (e.symm w)) = w 0) ∨
        (fibreBranchCount y = 2 ∧ ∀ w ∈ e.target,
          sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 * w 1) ∨
        (fibreBranchCount y = 3 ∧ ∀ w ∈ e.target,
          sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 * w 1 * w 2)) := by
  have hpos := fibreBranchCount_pos y
  have hle := fibreBranchCount_le_three y
  have hy : fibreBranchCount y = 1 ∨ fibreBranchCount y = 2 ∨ fibreBranchCount y = 3 := by
    omega
  rcases hy with hy | hy | hy
  · obtain ⟨e, hys, hzero, hsource, hprod⟩ := fibre_single_local_equation y hy
    exact ⟨e, hys, hzero, hsource, Or.inl ⟨hy, hprod⟩⟩
  · obtain ⟨e, hys, hzero, hsource, hprod⟩ := fibre_double_local_equation y hy
    exact ⟨e, hys, hzero, hsource, Or.inr (Or.inl ⟨hy, hprod⟩)⟩
  · obtain ⟨e, hys, hzero, hsource, hprod⟩ := fibre_triple_local_equation y hy
    exact ⟨e, hys, hzero, hsource, Or.inr (Or.inr ⟨hy, hprod⟩)⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms
