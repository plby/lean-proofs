import Mathlib.Topology.Homotopy.Lifting

/-!
# Fundamental groups of subspaces with connected covering preimage

Let `p : E → X` be a covering with simply connected total space. If the
preimage of a subspace `S` is path connected, every loop in `X` based in `S`
is homotopic, relative to its endpoints, to a loop lying in `S`.
Consequently the inclusion of `S` induces a surjection on fundamental groups.

The proof uses actual path lifting and endpoint-preserving homotopies; no
presentation of either fundamental group is assumed.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] {p : E → X}

/-- A loop at the image of a chosen lift can be replaced by a homotopic loop
in any subspace whose covering preimage is path connected. -/
theorem covering_exists_restricted_loop_homotopic (hp : IsCoveringMap p)
    (S : Set X) (hS : IsPathConnected (p ⁻¹' S)) (e : E) (he : p e ∈ S)
    (γ : Path (p e) (p e)) :
    ∃ δ : Path (⟨p e, he⟩ : S) ⟨p e, he⟩,
      (δ.map continuous_subtype_val).Homotopic γ := by
  obtain ⟨Γ, hΓ, hΓ₀⟩ := hp.exists_path_lifts γ e γ.source
  have hΓ₁ : p (Γ 1) = p e := (congr_fun hΓ 1).trans γ.target
  let Γ' : Path e (Γ 1) := ⟨Γ, hΓ₀, rfl⟩
  obtain ⟨Δ, hΔ⟩ := hS.joinedIn e he (Γ 1) (by
    change p (Γ 1) ∈ S
    rwa [hΓ₁])
  let δ : Path (⟨p e, he⟩ : S) ⟨p e, he⟩ :=
    { toFun t := ⟨p (Δ t), hΔ t⟩
      continuous_toFun := (hp.continuous.comp Δ.continuous).subtype_mk _
      source' := Subtype.ext (congrArg p Δ.source)
      target' := Subtype.ext ((congrArg p Δ.target).trans hΓ₁) }
  have hδ : δ.map continuous_subtype_val =
      (Δ.map hp.continuous).cast rfl hΓ₁.symm := by
    ext t
    rfl
  have hγ : (Γ'.map hp.continuous).cast rfl hΓ₁.symm = γ := by
    ext t
    exact congr_fun hΓ t
  have H := ((SimplyConnectedSpace.paths_homotopic Δ Γ').map
    (⟨p, hp.continuous⟩ : C(E, X))).pathCast rfl hΓ₁.symm
  exact ⟨δ, by simpa only [← hδ, hγ] using H⟩

/-- Surjectivity on the fundamental group at the image of a specified lift.
This form does not require global surjectivity of the covering map. -/
theorem covering_restriction_fundamentalGroup_map_surjective_at
    (hp : IsCoveringMap p) (S : Set X) (hS : IsPathConnected (p ⁻¹' S))
    (e : E) (he : p e ∈ S) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) ⟨p e, he⟩) := by
  intro γ
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    obtain ⟨δ, hδ⟩ := covering_exists_restricted_loop_homotopic hp S hS e he γ
    exact ⟨Path.Homotopic.Quotient.mk δ, Path.Homotopic.Quotient.eq.mpr hδ⟩

/-- A subspace with path-connected preimage in a simply connected covering
surjects onto the ambient fundamental group under its actual inclusion. -/
theorem covering_restriction_fundamentalGroup_map_surjective
    (hp : IsCoveringMap p) (hps : Function.Surjective p)
    (S : Set X) (hS : IsPathConnected (p ⁻¹' S)) (x : S) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) x) := by
  rcases x with ⟨x, hx⟩
  obtain ⟨e, rfl⟩ := hps x
  exact covering_restriction_fundamentalGroup_map_surjective_at hp S hS e hx

end Wikipedia.HopfProblem
