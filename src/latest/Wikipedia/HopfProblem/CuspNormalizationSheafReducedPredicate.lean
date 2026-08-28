import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic

/-!
# Locally ambient-holomorphic functions on an actual subset

The functions here are actual complex-valued functions on relative open
sets of a subset of a complex-charted space. Their defining property is
local extension to actual ambient holomorphic sections. No normalization
map or kernel presentation is used in this definition.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- Actual local ambient holomorphic extension, at every point of the
relative open domain. Equality is required on the actual intersection
with the ambient neighbourhood, not merely on a formal model. -/
def IsLocallyAmbient (U : Opens S) (f : U → ℂ) : Prop :=
  ∀ x : U, ∃ V : Opens M, x.val.val ∈ V ∧
    ∃ g : HolomorphicFunctionSheaf.Section I M V,
      ∀ (y : U) (hy : y.val.val ∈ V), f y = g ⟨y.val.val, hy⟩

/-- Restricting an actual function preserves its local ambient extensions. -/
theorem IsLocallyAmbient.restrict {U V : Opens S} (h : U ≤ V)
    {f : V → ℂ} (hf : IsLocallyAmbient I S V f) :
    IsLocallyAmbient I S U (fun x => f (Set.inclusion h x)) := by
  intro x
  obtain ⟨W, hxW, g, hg⟩ := hf (Set.inclusion h x)
  exact ⟨W, hxW, g, fun y hy => hg (Set.inclusion h y) hy⟩

/-- Constant functions have actual constant ambient representatives. -/
theorem IsLocallyAmbient.const (U : Opens S) (c : ℂ) :
    IsLocallyAmbient I S U (fun _ => c) := by
  intro x
  exact ⟨⊤, trivial, ⟨fun _ => c, contMDiff_const⟩, fun _ _ => rfl⟩

/-- The sum of locally ambient holomorphic functions has the sum of
their actual representatives on the intersection of two neighbourhoods. -/
theorem IsLocallyAmbient.add {U : Opens S} {f g : U → ℂ}
    (hf : IsLocallyAmbient I S U f) (hg : IsLocallyAmbient I S U g) :
    IsLocallyAmbient I S U (f + g) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := hf x
  obtain ⟨W, hxW, ψ, hψ⟩ := hg x
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩,
    ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ inf_le_left φ +
      ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ inf_le_right ψ, ?_⟩
  intro y hy
  change f y + g y = φ ⟨y.val.val, hy.1⟩ + ψ ⟨y.val.val, hy.2⟩
  rw [hφ y hy.1, hψ y hy.2]

/-- Products use the actual products of ambient holomorphic sections. -/
theorem IsLocallyAmbient.mul {U : Opens S} {f g : U → ℂ}
    (hf : IsLocallyAmbient I S U f) (hg : IsLocallyAmbient I S U g) :
    IsLocallyAmbient I S U (f * g) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := hf x
  obtain ⟨W, hxW, ψ, hψ⟩ := hg x
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩,
    ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ inf_le_left φ *
      ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ inf_le_right ψ, ?_⟩
  intro y hy
  change f y * g y = φ ⟨y.val.val, hy.1⟩ * ψ ⟨y.val.val, hy.2⟩
  rw [hφ y hy.1, hψ y hy.2]

/-- Negation preserves actual local ambient holomorphic extension. -/
theorem IsLocallyAmbient.neg {U : Opens S} {f : U → ℂ}
    (hf : IsLocallyAmbient I S U f) : IsLocallyAmbient I S U (-f) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := hf x
  exact ⟨V, hxV, -φ, fun y hy => congrArg Neg.neg (hφ y hy)⟩

/-- Restriction of any actual ambient holomorphic section to a relative
open subset of its domain satisfies the defining local condition. -/
theorem IsLocallyAmbient.of_ambient (U : Opens S) (V : Opens M)
    (g : HolomorphicFunctionSheaf.Section I M V)
    (hU : ∀ x : U, x.val.val ∈ V) :
    IsLocallyAmbient I S U (fun x => g ⟨x.val.val, hU x⟩) := by
  intro x
  exact ⟨V, hU x, g, fun _ _ => rfl⟩

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
