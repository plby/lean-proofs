import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRestrictionBasic
import Wikipedia.HopfProblem.CuspPuncturedCovering

/-!
# Restricting an actual filling overlap to a smaller base patch

The partial biholomorphism of the restricted filling is the composition
of its actual open inclusion with the original filling overlap.  Base
preservation identifies its target with the full inverse image of the
smaller base patch in the regular piece.  Both maps remain holomorphic
for the inherited native charts.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Restriction

variable {B X R E : Type*} [TopologicalSpace B] [TopologicalSpace X]
    [TopologicalSpace R] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [ChartedSpace E X] [ChartedSpace E R]

/-- Base preservation of an actual partial biholomorphism also holds
for its inverse on the full target. -/
theorem symm_preserves_base (p : C(X, B)) (pR : C(R, B))
    (e : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) X R ω)
    (hbase : ∀ x ∈ e.source, pR (e x) = p x) (y : R) (hy : y ∈ e.target) :
    p (e.symm y) = pR y := by
  have h := hbase (e.symm y) (e.map_target hy)
  have he : e (e.symm y) = y := e.right_inv hy
  exact h.symm.trans (congrArg pR he)

variable (p : C(X, B)) (V : Opens B) (hV : Nonempty (restrictedPiece p V))
    (e : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) X R ω)

/-- The actual partial biholomorphism from the restricted filling to
the unchanged regular piece. -/
def overlap : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
    (restrictedPiece p V) R ω :=
  (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ E)
    (restrictedPiece p V) hV).trans e

@[simp] theorem overlap_apply (x : restrictedPiece p V) :
    overlap p V hV e x = e x.val := rfl

theorem overlap_source :
    (overlap p V hV e).source = (Subtype.val : restrictedPiece p V → X) ⁻¹' e.source := by
  change univ ∩ (Subtype.val : restrictedPiece p V → X) ⁻¹' e.source = _
  exact univ_inter _

theorem overlap_target :
    (overlap p V hV e).target = e.target ∩ e.symm ⁻¹' (restrictedPiece p V : Set X) := by
  change e.target ∩ e.symm ⁻¹'
    ((restrictedPiece p V).openPartialHomeomorphSubtypeCoe hV).target = _
  rw [Opens.openPartialHomeomorphSubtypeCoe_target]

/-- Restriction leaves the complete regular-patch inverse image as
the source, now taken inside the actual smaller filling piece. -/
theorem overlap_source_eq (Breg : Opens B)
    (hsource : e.source = p ⁻¹' (Breg : Set B)) :
    (overlap p V hV e).source = restrictedProjection p V ⁻¹' (Breg : Set B) := by
  rw [overlap_source, hsource]
  rfl

/-- The restricted overlap still preserves the original base projection. -/
theorem overlap_preserves_base (pR : C(R, B))
    (hbase : ∀ x ∈ e.source, pR (e x) = p x)
    (x : restrictedPiece p V) (hx : x ∈ (overlap p V hV e).source) :
    pR (overlap p V hV e x) = restrictedProjection p V x := by
  exact hbase x.val (by simpa only [overlap_source, mem_preimage] using hx)

/-- The target is exactly the inverse image of the smaller base patch,
not merely a subset of the original overlap target. -/
theorem overlap_target_eq (pR : C(R, B)) (U : Opens B) (hVU : V ≤ U)
    (htarget : e.target = pR ⁻¹' (U : Set B))
    (hbase : ∀ x ∈ e.source, pR (e x) = p x) :
    (overlap p V hV e).target = pR ⁻¹' (V : Set B) := by
  rw [overlap_target]
  ext y
  constructor
  · rintro ⟨hy, hyV⟩
    change pR y ∈ V
    change p (e.symm y) ∈ V at hyV
    rwa [symm_preserves_base p pR e hbase y hy] at hyV
  · intro hy
    change pR y ∈ V at hy
    have hyU : y ∈ e.target := by
      rw [htarget]
      exact hVU hy
    refine ⟨hyU, ?_⟩
    change p (e.symm y) ∈ V
    rw [symm_preserves_base p pR e hbase y hyU]
    exact hy

/-- On the actual target, the inverse has exactly the original inverse
as its ambient point; only its type records membership in the smaller piece. -/
theorem overlap_symm_apply_val (y : R) (hy : y ∈ (overlap p V hV e).target) :
    ((overlap p V hV e).symm y : X) = e.symm y := by
  have hyV : e.symm y ∈ restrictedPiece p V := by
    rw [overlap_target] at hy
    exact hy.2
  change ((restrictedPiece p V).openPartialHomeomorphSubtypeCoe hV)
    (((restrictedPiece p V).openPartialHomeomorphSubtypeCoe hV).symm (e.symm y)) = _
  exact ((restrictedPiece p V).openPartialHomeomorphSubtypeCoe hV).right_inv (by
    simpa only [Opens.openPartialHomeomorphSubtypeCoe_target, SetLike.mem_coe] using hyV)

/-- Native forward holomorphy, in the exact form required by the star constructor. -/
theorem overlap_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (overlap p V hV e).toOpenPartialHomeomorph (overlap p V hV e).source :=
  (overlap p V hV e).contMDiffOn

/-- Native inverse holomorphy on the entire constructed target. -/
theorem overlap_symm_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (overlap p V hV e).toOpenPartialHomeomorph.symm (overlap p V hV e).target :=
  (overlap p V hV e).symm.contMDiffOn

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Restriction
