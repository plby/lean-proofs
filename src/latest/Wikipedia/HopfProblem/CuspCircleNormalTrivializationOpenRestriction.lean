import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Native open restrictions at arbitrary differentiability order

The original open-subtype atlases and literal inclusion inverses give
partial diffeomorphisms for any scalar field and differentiability order.
Consequently the actual local diffeomorphisms used for the normal
neighborhood can be restricted over the real field as well as the
complex field, without replacing their smooth structures.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.OpenRestriction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K) {n : ℕ∞ω}

/-- The actual open inclusion, with its original local inverse. -/
def opensInclusionPartialDiffeomorph (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M n := by
  let e := U.openPartialHomeomorphSubtypeCoe hU
  refine {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := ?_ }
  intro x hx
  have hxU : x ∈ U := by simpa [e] using hx
  have he : (Subtype.val ∘ e.symm) =ᶠ[𝓝 x] id := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    exact e.right_inv (by
      simpa only [e, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hy)
  have hs : ContMDiffAt I I n (Subtype.val ∘ e.symm) x :=
    contMDiffAt_id.congr_of_eventuallyEq he
  have hi : ContMDiffAt I I n (Subtype.val ∘ e.symm) x ↔
      ContMDiffAt I I n e.symm x := ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact (hi.mp hs).contMDiffWithinAt

theorem isLocalDiffeomorph_subtypeVal (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph I I n (Subtype.val : U → M) := by
  intro x
  refine ⟨opensInclusionPartialDiffeomorph I U ⟨x⟩, mem_univ _, ?_⟩
  intro y _
  rfl

/-- Codomain restriction preserves the actual local diffeomorphism at a point. -/
theorem isLocalDiffeomorphAt_codRestrictOpens {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (V : TopologicalSpace.Opens N)
    (hV : ∀ x, f x ∈ V) :
    IsLocalDiffeomorphAt I J n (fun y => (⟨f y, hV y⟩ : V)) x := by
  obtain ⟨Φ, hx, he⟩ := hf
  let eV := opensInclusionPartialDiffeomorph J (n := n) V ⟨⟨f x, hV x⟩⟩
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

theorem isLocalDiffeomorph_codRestrictOpens {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (V : TopologicalSpace.Opens N)
    (hV : ∀ x, f x ∈ V) :
    IsLocalDiffeomorph I J n (fun x => (⟨f x, hV x⟩ : V)) :=
  fun x => isLocalDiffeomorphAt_codRestrictOpens I J (hf x) V hV

/-- Restriction to the original open source and target, at any specified source point. -/
theorem isLocalDiffeomorphAt_restrictOpens {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hUV : MapsTo f (U : Set M) (V : Set N)) (hx : x ∈ U) :
    IsLocalDiffeomorphAt I J n (fun y : U => (⟨f y, hUV y.2⟩ : V)) ⟨x, hx⟩ := by
  have hU : IsLocalDiffeomorphAt I J n (fun y : U => f y) ⟨x, hx⟩ :=
    (isLocalDiffeomorph_subtypeVal I (n := n) U ⟨x, hx⟩).comp (K := J) (P := N) hf
  exact isLocalDiffeomorphAt_codRestrictOpens I J hU V (fun y => hUV y.2)

/-- A genuine local diffeomorphism restricts to any compatible open source and target. -/
theorem isLocalDiffeomorph_restrictOpens {f : M → N}
    (hf : IsLocalDiffeomorph I J n f)
    (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
    (hUV : MapsTo f (U : Set M) (V : Set N)) :
    IsLocalDiffeomorph I J n (fun x : U => (⟨f x, hUV x.2⟩ : V)) := by
  have hU : IsLocalDiffeomorph I J n (fun x : U => f x) := by
    intro x
    exact (isLocalDiffeomorph_subtypeVal I (n := n) U x).comp (K := J) (P := N) (hf x)
  exact isLocalDiffeomorph_codRestrictOpens I J hU V (fun x => hUV x.2)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.OpenRestriction
