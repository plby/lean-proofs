import Wikipedia.NoExoticSixSphere.SphereFamilyDiagonalClosure
import Mathlib.Data.Set.Card

/-!
# Compact ordered double-point pairs of an immersed three-sphere

The set contains only distinct source points with equal images. The proved
native immersion theorem excludes diagonal accumulation; continuity excludes
unequal image limits. Thus this original off-diagonal set is closed and
compact. Swapping the sheets is a fixed-point-free involution of the set.
Its cardinality is not identified with a geometric self-intersection here.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSelfIntersections

open GLOrthonormalization

variable {M : Type*}

def pairs (f : Sphere 3 → M) : Set (Sphere 3 × Sphere 3) :=
  {p | p.1 ≠ p.2 ∧ f p.1 = f p.2}

def swap (f : Sphere 3 → M) : pairs f → pairs f :=
  fun p ↦ ⟨p.val.swap, p.property.1.symm, p.property.2.symm⟩

theorem swap_involutive (f : Sphere 3 → M) : Involutive (swap f) :=
  fun _ ↦ Subtype.ext rfl

theorem swap_ne (f : Sphere 3 → M) (p : pairs f) : swap f p ≠ p := by
  intro h
  exact p.property.1 (congrArg (fun q : pairs f ↦ q.val.1) h).symm

variable [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

theorem isClosed_pairs {f : Sphere 3 → M} (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) : IsClosed (pairs f) := by
  let G : ℝ → Sphere 3 → M := fun _ ↦ f
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry G) :=
    hf.comp contMDiff_snd
  have heq : IsClosed {p : Sphere 3 × Sphere 3 | f p.1 = f p.2} :=
    isClosed_eq (hf.continuous.comp continuous_fst) (hf.continuous.comp continuous_snd)
  have hmap : MapsTo (fun p : Sphere 3 × Sphere 3 ↦ ((0 : ℝ), p)) (pairs f)
      (FamilyEmbedding.doublePoints G) := fun _ hp ↦ hp
  apply isClosed_of_closure_subset
  rintro ⟨x, y⟩ hp
  refine ⟨?_, closure_minimal (fun _ h ↦ h.2) heq hp⟩
  change x ≠ y
  intro hxy
  subst y
  have hcl := hmap.closure (continuous_const.prodMk continuous_id) hp
  exact SphereFamily.diagonal_not_mem_closure G hG (0, x) (hi x) hcl

theorem isCompact_pairs {f : Sphere 3 → M} (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) : IsCompact (pairs f) :=
  (isClosed_pairs hf hi).isCompact

end NoExoticSixSphere.SphereSelfIntersections
