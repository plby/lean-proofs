import StackExchange.Puzzling139335.BoundaryGerm
import StackExchange.Puzzling139335.JordanTransport
import Wikipedia.SchoenfliesTheorem.JordanSeparates

/-!
# Counting the straight branches at a Jordan-boundary point

A cut pair displays the two local branches.  The count is initially an
existential relation; independence of the chosen cut will be proved from
local branch matching.
-/

open Set

namespace Puzzling139335

/-- The contribution of one endpoint branch to the straight-branch count. -/
noncomputable def straightGermIndicator (A : Set Plane) (v : Plane) : ℕ := by
  classical
  exact if IsStraightAt A v then 1 else 0

theorem straightGermIndicator_le_one (A : Set Plane) (v : Plane) :
    straightGermIndicator A v ≤ 1 := by
  classical
  unfold straightGermIndicator
  split <;> omega

theorem straightGermIndicator_eq_one_iff (A : Set Plane) (v : Plane) :
    straightGermIndicator A v = 1 ↔ IsStraightAt A v := by
  classical
  simp [straightGermIndicator]

theorem straightGermIndicator_eq_zero_iff (A : Set Plane) (v : Plane) :
    straightGermIndicator A v = 0 ↔ ¬ IsStraightAt A v := by
  classical
  simp [straightGermIndicator]

theorem SameBoundaryGerm.straightGermIndicator_eq {A B : Set Plane} {v : Plane}
    (h : SameBoundaryGerm A B v) : straightGermIndicator A v = straightGermIndicator B v := by
  classical
  simp only [straightGermIndicator, h.isStraightAt_iff]

theorem straightGermIndicator_image_affineIsometry (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (A : Set Plane) (v : Plane) :
    straightGermIndicator (e '' A) (e v) = straightGermIndicator A v := by
  classical
  simp only [straightGermIndicator, isStraightAt_image_affineIsometry_iff]

/-- A Jordan curve has `n` straight branches at `v` if one cut pair based at
`v` displays precisely that many straight initial arcs. -/
def HasStraightBranchCount (C : Set Plane) (v : Plane) (n : ℕ) : Prop :=
  ∃ q A B, Schoenflies.IsCutPair C v q A B ∧
    n = straightGermIndicator A v + straightGermIndicator B v

namespace HasStraightBranchCount

theorem le_two {C : Set Plane} {v : Plane} {n : ℕ}
    (h : HasStraightBranchCount C v n) : n ≤ 2 := by
  obtain ⟨q, A, B, _, rfl⟩ := h
  have hA := straightGermIndicator_le_one A v
  have hB := straightGermIndicator_le_one B v
  omega

theorem image_affineIsometry {C : Set Plane} {v : Plane} {n : ℕ}
    (h : HasStraightBranchCount C v n) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    HasStraightBranchCount (e '' C) (e v) n := by
  obtain ⟨q, A, B, hcut, hn⟩ := h
  have hcut' := hcut.image_homeomorph e.toHomeomorph
  change Schoenflies.IsCutPair (e '' C) (e v) (e q) (e '' A) (e '' B) at hcut'
  refine ⟨e q, e '' A, e '' B, hcut', ?_⟩
  simpa only [straightGermIndicator_image_affineIsometry] using hn

theorem mem {C : Set Plane} {v : Plane} {n : ℕ}
    (h : HasStraightBranchCount C v n) : v ∈ C := by
  obtain ⟨q, A, B, hcut, _⟩ := h
  rw [← hcut.union_eq]
  exact Or.inl hcut.fst.left_mem

end HasStraightBranchCount

theorem exists_straightBranchCount {C : Set Plane} (hC : Schoenflies.IsJordanCurve C)
    {v : Plane} (hv : v ∈ C) : ∃ n, HasStraightBranchCount C v n := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hC.exists_ne
  have hex : ∃ q ∈ C, v ≠ q := by
    by_cases hvx : v = x
    · exact ⟨y, hy, hvx ▸ hxy⟩
    · exact ⟨x, hx, hvx⟩
  obtain ⟨q, hq, hvq⟩ := hex
  obtain ⟨A, B, hcut⟩ := Schoenflies.exists_isCutPair hC hv hq hvq
  exact ⟨straightGermIndicator A v + straightGermIndicator B v, q, A, B, hcut, rfl⟩

theorem hasStraightBranchCount_image_affineIsometry_iff
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (C : Set Plane) (v : Plane) (n : ℕ) :
    HasStraightBranchCount (e '' C) (e v) n ↔ HasStraightBranchCount C v n := by
  constructor
  · intro h
    have h' := h.image_affineIsometry e.symm
    simpa only [image_image, e.symm_apply_apply, Function.comp_def, image_id'] using h'
  · exact fun h => h.image_affineIsometry e

end Puzzling139335
