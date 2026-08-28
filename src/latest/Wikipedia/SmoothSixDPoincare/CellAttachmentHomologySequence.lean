import Wikipedia.SmoothSixDPoincare.CellAttachmentHomologyMaps

/-!
# The actual positive-degree cell-attachment homology sequence

Transfer the proved open-cover Mayer–Vietoris sequence through the actual
old-neighborhood and annular homotopy equivalences. The disk patch's
positive-degree homology vanishes. Thus the resulting maps are precisely
the original attaching-sphere and old-space inclusion maps.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

theorem range_coverRight (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (rightHomologyMap D.oldNeighborhood D.diskPatch k) =
      LinearMap.range (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k).symm b.1, (D.coverRight_formula k hk b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k b, 0), D.coverRight_old k b⟩

/-- Exactness at the homology of the original old space, in every positive degree. -/
theorem cell_exact_at_old (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (D.attachingHomologyMap k) = LinearMap.ker (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    have hzero := LinearMap.congr_fun
      (leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch k) (D.overlapHomologyEquiv k s)
    change rightHomologyMap D.oldNeighborhood D.diskPatch k
      (leftHomologyMap D.oldNeighborhood D.diskPatch k (D.overlapHomologyEquiv k s)) = 0 at hzero
    rw [D.coverLeft_formula k hk, D.coverRight_old] at hzero
    exact hzero
  · intro ha
    have hpair : (D.oldHomologyEquiv k a, 0) ∈
        LinearMap.ker (rightHomologyMap D.oldNeighborhood D.diskPatch k) := by
      change rightHomologyMap D.oldNeighborhood D.diskPatch k (D.oldHomologyEquiv k a, 0) = 0
      rw [D.coverRight_old]
      exact ha
    rw [← exact_at_pair D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k] at hpair
    obtain ⟨c, hc⟩ := hpair
    refine ⟨(D.overlapHomologyEquiv k).symm c, ?_⟩
    have hc' : leftHomologyMap D.oldNeighborhood D.diskPatch k
        (D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm c)) =
        (D.oldHomologyEquiv k a, 0) := by
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    rw [D.coverLeft_formula k hk] at hc'
    have heq := congrArg
      (fun b : SingularHomology D.oldNeighborhood k × SingularHomology D.diskPatch k => b.1) hc'
    exact (D.oldHomologyEquiv k).injective heq

/-- Exactness at the actual ambient homology in every positive degree. -/
theorem cell_exact_at_ambient (k : ℕ) :
    LinearMap.range (D.oldHomologyMap (k + 1)) = LinearMap.ker (D.cellConnectingMap k) := by
  rw [← D.range_coverRight (k + 1) (Nat.succ_ne_zero k),
    exact_at_ambient D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k]
  ext a
  exact (D.cellConnecting_eq_zero_iff k a).symm

theorem mem_range_cellConnecting (k : ℕ) (a : SingularHomology (sphere (0 : N) 1) k) :
    a ∈ LinearMap.range (D.cellConnectingMap k) ↔
      D.overlapHomologyEquiv k a ∈ LinearMap.range
        (connectingHomomorphism D.oldNeighborhood D.diskPatch
          D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change _ = D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm _)
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change (D.overlapHomologyEquiv k).symm _ = a
    rw [hx, LinearEquiv.symm_apply_apply]

theorem coverLeft_eq_zero_iff (k : ℕ) (hk : k ≠ 0)
    (a : SingularHomology (sphere (0 : N) 1) k) :
    leftHomologyMap D.oldNeighborhood D.diskPatch k (D.overlapHomologyEquiv k a) = 0 ↔
      D.attachingHomologyMap k a = 0 := by
  rw [D.coverLeft_formula k hk]
  constructor
  · intro h
    have heq := congrArg
      (fun b : SingularHomology D.oldNeighborhood k × SingularHomology D.diskPatch k => b.1) h
    exact (D.oldHomologyEquiv k).injective (heq.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]
    rfl

/-- The connecting map lands in precisely the kernel of the original attaching-sphere map. -/
theorem cell_exact_at_sphere (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (D.cellConnectingMap k) = LinearMap.ker (D.attachingHomologyMap k) := by
  ext a
  rw [D.mem_range_cellConnecting k,
    exact_at_intersection D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k]
  exact D.coverLeft_eq_zero_iff k hk a

end Wikipedia.SmoothSixDPoincare.EmbeddedCellAttachment
