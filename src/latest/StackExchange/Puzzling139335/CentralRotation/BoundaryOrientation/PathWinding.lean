import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.Winding

/-!
# Winding under concatenation of plane paths

The common boundary cut is canceled as an actual path and its reversal.
The lemmas apply to arbitrary continuous paths avoiding the reference point.
-/

open Set unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

theorem avoids_trans {p q r x : Plane} (M : Path p q) (N : Path q r)
    (hM : ∀ t, M t ≠ x) (hN : ∀ t, N t ≠ x) :
    ∀ t, (M.trans N) t ≠ x := by
  intro t h
  have hx : x ∈ range M ∪ range N := by
    rw [← Path.trans_range]
    exact ⟨t, h⟩
  rcases hx with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact hM s hs
  · exact hN s hs

theorem avoids_symm {p q x : Plane} (M : Path p q) (hM : ∀ t, M t ≠ x) :
    ∀ t, M.symm t ≠ x := fun t => hM (σ t)

private theorem continuousOn_directionAt_path {p q x : Plane} (M : Path p q)
    (hM : ∀ t, M t ≠ x) : ContinuousOn (directionAt x) (range M) := by
  apply (continuousOn_directionAt x).mono
  rintro _ ⟨t, rfl⟩
  exact hM t

/-- A plane path lifted to its angular path about a point it avoids. -/
def angularPath {p q : Plane} (M : Path p q) (x : Plane) (hM : ∀ t, M t ≠ x) :
    Path (directionAt x p) (directionAt x q) :=
  M.map' (continuousOn_directionAt_path M hM)

@[simp] theorem angularPath_apply {p q : Plane} (M : Path p q) (x : Plane)
    (hM : ∀ t, M t ≠ x) (t : I) : angularPath M x hM t = directionAt x (M t) := rfl

theorem directionPath_eq_angularPath {p q : Plane} (M : Path p q) (x : Plane)
    (hM : ∀ t, M t ≠ x) :
    directionPath M x hM = (angularPath M x hM : C(I, AddCircle (1 : ℝ))) := by
  ext t
  exact directionPath_apply M x hM t

theorem angularPath_trans {p q r : Plane} (M : Path p q) (N : Path q r)
    (x : Plane) (hM : ∀ t, M t ≠ x) (hN : ∀ t, N t ≠ x)
    (hMN : ∀ t, (M.trans N) t ≠ x) :
    angularPath (M.trans N) x hMN = (angularPath M x hM).trans (angularPath N x hN) := by
  ext t
  rw [angularPath_apply, Path.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

theorem angularPath_symm {p q : Plane} (M : Path p q) (x : Plane)
    (hM : ∀ t, M t ≠ x) (hMs : ∀ t, M.symm t ≠ x) :
    angularPath M.symm x hMs = (angularPath M x hM).symm := by
  ext t
  rfl

/-- Angular lift displacements add along a concatenation of actual plane paths. -/
theorem winding_trans {p q r : Plane} (M : Path p q) (N : Path q r)
    (x : Plane) (hM : ∀ t, M t ≠ x) (hN : ∀ t, N t ≠ x)
    (hMN : ∀ t, (M.trans N) t ≠ x) :
    winding (M.trans N) x hMN = winding M x hM + winding N x hN := by
  unfold winding
  rw [directionPath_eq_angularPath, directionPath_eq_angularPath,
    directionPath_eq_angularPath, angularPath_trans M N x hM hN hMN,
    CircleDegree.displacement_trans]

theorem winding_symm {p q : Plane} (M : Path p q) (x : Plane)
    (hM : ∀ t, M t ≠ x) (hMs : ∀ t, M.symm t ≠ x) :
    winding M.symm x hMs = -winding M x hM := by
  unfold winding
  rw [directionPath_eq_angularPath, directionPath_eq_angularPath,
    angularPath_symm M x hM hMs, CircleDegree.displacement_symm]

/-- Cancellation of the two opposite traversals of an actual shared cut. -/
theorem winding_boundary_gluing {p q : Plane} (M : Path p q) (Γ N : Path q p)
    (x : Plane) (hM : ∀ t, M t ≠ x) (hΓ : ∀ t, Γ t ≠ x)
    (hN : ∀ t, N t ≠ x)
    (hA : ∀ t, (M.trans Γ) t ≠ x)
    (hB : ∀ t, (Γ.symm.trans N) t ≠ x)
    (hU : ∀ t, (M.trans N) t ≠ x) :
    winding (M.trans Γ) x hA + winding (Γ.symm.trans N) x hB =
      winding (M.trans N) x hU := by
  rw [winding_trans M Γ x hM hΓ hA,
    winding_trans Γ.symm N x (avoids_symm Γ hΓ) hN hB,
    winding_trans M N x hM hN hU,
    winding_symm Γ x hΓ (avoids_symm Γ hΓ)]
  ring

end

end Puzzling139335.CentralRotation.BoundaryOrientation
