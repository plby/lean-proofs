import Wikipedia.HopfProblem.CoveringManifold
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Analytic local diffeomorphisms for quotient coverings and open restrictions

The projection to the analytic quotient atlas is locally biholomorphic:
its inverse branches are precisely the holomorphic covering lifts already
used to construct that atlas.  The same property is preserved by restricting
the source and target to open subsets with their inherited complex charts.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

namespace CoveringQuotient

variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
    [Group G] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G)
    [IsManifold (modelWithCornersSelf ℂ E) ω M]

theorem project_isLocalDiffeomorph
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (fun x : M => g • x)) :
    letI := chartedSpace (E := E) hq
    IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω q := by
  let := chartedSpace (E := E) hq
  intro x
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) M Q ω :=
    { toPartialEquiv := (localInverse hq x).symm.toPartialEquiv
      open_source := (localInverse hq x).open_target
      open_target := (localInverse hq x).open_source
      contMDiffOn_toFun := by
        change ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
          (localInverse hq x).symm (localInverse hq x).target
        rw [localInverse_symm]
        exact (contMDiff_project hq ω hG).contMDiffOn
      contMDiffOn_invFun := localInverse_holomorphic hq ω hG x }
  refine ⟨Φ, hq.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target, ?_⟩
  intro y _
  change q y = (localInverse hq x).symm y
  rw [localInverse_symm]

end CoveringQuotient

section RestrictOpens

variable {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)

/-- The inclusion of an open subset, viewed as an analytic partial
diffeomorphism onto that open subset of the ambient manifold. -/
def opensInclusionPartialDiffeomorph (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M ω := by
  let e := U.openPartialHomeomorphSubtypeCoe hU
  refine
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := ?_ }
  intro x hx
  have hxU : x ∈ U := by
    simpa [e] using hx
  have he : (Subtype.val ∘ e.symm) =ᶠ[𝓝 x] id := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    exact e.right_inv (by
      simpa only [e, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hy)
  have hs : ContMDiffAt I I ω (Subtype.val ∘ e.symm) x :=
    contMDiffAt_id.congr_of_eventuallyEq he
  have hi : ContMDiffAt I I ω (Subtype.val ∘ e.symm) x ↔
      ContMDiffAt I I ω e.symm x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact (hi.mp hs).contMDiffWithinAt

theorem isLocalDiffeomorph_subtypeVal (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph I I ω (Subtype.val : U → M) := by
  intro x
  refine ⟨opensInclusionPartialDiffeomorph I U ⟨x⟩, mem_univ _, ?_⟩
  intro y _
  rfl

/-- Restricting only the codomain to an open subset that contains the image
preserves being a local analytic diffeomorphism at the specified point. -/
theorem isLocalDiffeomorphAt_codRestrictOpens {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ω f x) (V : TopologicalSpace.Opens N)
    (hV : ∀ x, f x ∈ V) :
    IsLocalDiffeomorphAt I J ω (fun y => (⟨f y, hV y⟩ : V)) x := by
  obtain ⟨Φ, hx, he⟩ := hf
  let eV := opensInclusionPartialDiffeomorph J V ⟨⟨f x, hV x⟩⟩
  let Ψ := Φ.trans eV.symm
  have hxV : Φ x ∈ V := by
    rw [← he hx]
    exact hV x
  have hxV' : Φ x ∈ (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).target := by
    simpa using hxV
  refine ⟨Ψ, ⟨hx, hxV'⟩, ?_⟩
  intro y hy
  have hyV : Φ y ∈ (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).target := hy.2
  apply Subtype.ext
  change f y = ((V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).symm (Φ y) : N)
  have hv := (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).right_inv hyV
  exact (he hy.1).trans hv.symm

/-- Restricting only the codomain to an open subset that contains the image
preserves the local analytic diffeomorphism property. -/
theorem isLocalDiffeomorph_codRestrictOpens {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (V : TopologicalSpace.Opens N)
    (hV : ∀ x, f x ∈ V) :
    IsLocalDiffeomorph I J ω (fun x => (⟨f x, hV x⟩ : V)) :=
  fun x => isLocalDiffeomorphAt_codRestrictOpens I J (hf x) V hV

/-- The open-restriction construction only needs a local analytic inverse
at the point under consideration, not at every point of the ambient map. -/
theorem isLocalDiffeomorphAt_restrictOpens {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ω f x)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hUV : MapsTo f (U : Set M) (V : Set N)) (hx : x ∈ U) :
    IsLocalDiffeomorphAt I J ω (fun y : U => (⟨f y, hUV y.2⟩ : V)) ⟨x, hx⟩ := by
  have hU : IsLocalDiffeomorphAt I J ω (fun y : U => f y) ⟨x, hx⟩ :=
    (isLocalDiffeomorph_subtypeVal I U ⟨x, hx⟩).comp (K := J) (P := N) hf
  exact isLocalDiffeomorphAt_codRestrictOpens I J hU V (fun y => hUV y.2)

/-- A local analytic diffeomorphism restricts to any open source and target
to which it maps. Both subtype atlases are inherited from their ambients. -/
theorem isLocalDiffeomorph_restrictOpens {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hUV : MapsTo f (U : Set M) (V : Set N)) :
    IsLocalDiffeomorph I J ω (fun x : U => (⟨f x, hUV x.2⟩ : V)) := by
  have hU : IsLocalDiffeomorph I J ω (fun x : U => f x) := by
    intro x
    exact (isLocalDiffeomorph_subtypeVal I U x).comp (K := J) (P := N) (hf x)
  exact isLocalDiffeomorph_codRestrictOpens I J hU V (fun x => hUV x.2)

end RestrictOpens

end Wikipedia.HopfProblem
