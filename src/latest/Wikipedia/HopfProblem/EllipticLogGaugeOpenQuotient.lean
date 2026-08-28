import Wikipedia.HopfProblem.EllipticLogGaugeQuotientCore
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# Invariant open subsets and the actual open part of a finite quotient

The quotient of an invariant open subset is analytically identified with
the corresponding open subset of the whole quotient.  The latter keeps
the atlas inherited from the whole quotient; it is not assigned a new
atlas by the comparison map.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

variable (G : Type*) [Group G] {M : Type*} [TopologicalSpace M] [MulAction G M]
    (U : TopologicalSpace.Opens M) [MulAction G U]
    (V : TopologicalSpace.Opens (FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre : FiniteQuotient.project G M ⁻¹' (V : Set (FiniteQuotient.Space G M)) = (U : Set M))

def restrictedProject (x : U) : V :=
  ⟨FiniteQuotient.project G M x, by
    change (x : M) ∈ FiniteQuotient.project G M ⁻¹' (V : Set (FiniteQuotient.Space G M))
    rw [hpre]
    exact x.2⟩

omit [MulAction G U] in
@[simp] theorem restrictedProject_coe (x : U) :
    (restrictedProject G U V hpre x : FiniteQuotient.Space G M) =
      FiniteQuotient.project G M x := rfl

omit [MulAction G U] in
theorem restrictedProject_surjective : Function.Surjective (restrictedProject G U V hpre) := by
  intro y
  obtain ⟨x, hx⟩ := FiniteQuotient.project_surjective G M y.1
  have hxU : x ∈ (U : Set M) := by
    rw [← hpre]
    change FiniteQuotient.project G M x ∈ (V : Set (FiniteQuotient.Space G M))
    rw [hx]
    exact y.2
  exact ⟨⟨x, hxU⟩, Subtype.ext hx⟩

def openQuotientEquiv : FiniteQuotient.Space G U ≃ V :=
  (Equiv.subtypeQuotientEquivQuotientSubtype
    (fun x : M => x ∈ (U : Set M)) (s₁ := MulAction.orbitRel G M)
    (s₂ := MulAction.orbitRel G U)
    (fun y => y ∈ (V : Set (FiniteQuotient.Space G M)))
    (by
      intro x
      change x ∈ (U : Set M) ↔ x ∈ FiniteQuotient.project G M ⁻¹' (V : Set _)
      rw [hpre])
    (by
      intro x y
      change (x ∈ MulAction.orbit G y) ↔ ((x : M) ∈ MulAction.orbit G (y : M))
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, (hcompat g y).symm.trans (congrArg Subtype.val hg)⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, Subtype.ext ((hcompat g y).trans hg)⟩)).symm

@[simp] theorem openQuotientEquiv_project (x : U) :
    openQuotientEquiv G U V hcompat hpre (FiniteQuotient.project G U x) =
      restrictedProject G U V hpre x := rfl

@[simp] theorem openQuotientEquiv_symm_restrictedProject (x : U) :
    (openQuotientEquiv G U V hcompat hpre).symm (restrictedProject G U V hpre x) =
      FiniteQuotient.project G U x := by
  rw [← openQuotientEquiv_project G U V hcompat hpre x, Equiv.symm_apply_apply]

include hcompat in
theorem subtypeAction_isCancelSMul [IsCancelSMul G M] : IsCancelSMul G U where
  right_cancel' g h x he := by
    apply IsCancelSMul.right_cancel g h (x : M)
    simpa only [hcompat] using congrArg Subtype.val he

section ComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))

include hcompat hM in
theorem subtypeAction_holomorphic (g : G) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : U => g • x) := by
  intro x
  have hi : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (fun y : U => ((g • y : U) : M)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (fun y : U => g • y) x := ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply hi.mp
  simpa only [hcompat, Function.comp_def] using
    ((hM g).comp contMDiff_subtype_val).contMDiffAt (x := x)

include hcompat hM in
theorem subtypeAction_continuousConstSMul : ContinuousConstSMul G U where
  continuous_const_smul g := (subtypeAction_holomorphic G U hcompat hM g).continuous

variable [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] [IsCancelSMul G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M]

include hM in
omit [MulAction G U] in
theorem restrictedProject_isLocalDiffeomorph :
    letI := FiniteQuotient.chartedSpace (E := E) G M
    IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (restrictedProject G U V hpre) := by
  let := FiniteQuotient.chartedSpace (E := E) G M
  have hUV : MapsTo (FiniteQuotient.project G M) (U : Set M) (V : Set _) := by
    intro x hx
    change x ∈ FiniteQuotient.project G M ⁻¹' (V : Set _)
    rwa [hpre]
  exact isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
    (CoveringQuotient.project_isLocalDiffeomorph
      (FiniteQuotient.project_isQuotientCoveringMap G M) hM) U V hUV

/-- The actual quotient of the invariant open set is biholomorphic to the
actual open submanifold of the whole finite quotient. -/
def openQuotientBiholomorph :
    letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
    letI := subtypeAction_continuousConstSMul G U hcompat hM
    letI := subtypeAction_isCancelSMul G U hcompat
    letI := FiniteQuotient.chartedSpace (E := E) G M
    letI := FiniteQuotient.chartedSpace (E := E) G U
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      (FiniteQuotient.Space G U) V ω := by
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let := subtypeAction_continuousConstSMul G U hcompat hM
  let := subtypeAction_isCancelSMul G U hcompat
  let := FiniteQuotient.chartedSpace (E := E) G M
  let := FiniteQuotient.chartedSpace (E := E) G U
  have hr := restrictedProject_isLocalDiffeomorph G U V hpre hM
  refine
    { toEquiv := openQuotientEquiv G U V hcompat hpre
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply CoveringQuotient.contMDiff_of_comp
      (FiniteQuotient.project_isQuotientCoveringMap G U) (modelWithCornersSelf ℂ E) ω
    exact hr.contMDiff
  · apply contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) hr
      (restrictedProject_surjective G U V hpre)
    have he : (openQuotientEquiv G U V hcompat hpre).symm ∘ restrictedProject G U V hpre =
        FiniteQuotient.project G U := by
      funext x
      exact openQuotientEquiv_symm_restrictedProject G U V hcompat hpre x
    rw [he]
    exact FiniteQuotient.project_holomorphic G U (subtypeAction_holomorphic G U hcompat hM)

@[simp] theorem openQuotientBiholomorph_project (x : U) :
    openQuotientBiholomorph G U V hcompat hpre hM (FiniteQuotient.project G U x) =
      restrictedProject G U V hpre x := rfl

@[simp] theorem openQuotientBiholomorph_project_coe (x : U) :
    (openQuotientBiholomorph G U V hcompat hpre hM (FiniteQuotient.project G U x) :
      FiniteQuotient.Space G M) = FiniteQuotient.project G M x := rfl

end ComplexStructure

end Wikipedia.HopfProblem.Elliptic.LogGauge
