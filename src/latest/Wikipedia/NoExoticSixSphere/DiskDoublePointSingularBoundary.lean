import Wikipedia.NoExoticSixSphere.DiskDoublePointBoundaryCurve

/-!
# The original disk singularities are exactly its diagonal boundary orbits

Each original native singularity gives its actual diagonal point in the
double-point closure. The orbit of this point is neither duplicated nor
identified with a different singularity. Conversely every diagonal orbit
comes from an original native singularity in the closed disk.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskDoublePoints

open GLOrthonormalization InvolutionQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

abbrev singularSet (g : Vector 4 → M) : Set (Vector 4) :=
  closedBall 0 1 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}

variable (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
  (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (ρ : ℝ) (hρ1 : ρ < 1)
  (hi : ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x))
  (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
  (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
  (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
    (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source})

def singularOrbit (x : singularSet g) : diagonalOrbits g :=
  ⟨unorderedProj g ⟨(x.val, x.val),
    singular_diagonal_mem_closure e g hg ρ hρ1 hi C hC hgen x.val x.property.1 x.property.2⟩,
    (mem_diagonalOrbits_iff g _).mpr rfl⟩

theorem injective_singularOrbit :
    Injective (singularOrbit e g hg ρ hρ1 hi C hC hgen) := by
  intro a b he
  have heq := congrArg Subtype.val he
  rcases (proj_eq_iff (swapClosure g) (swapClosure_involutive g) _ _).mp heq with heq | heq
  · exact Subtype.ext (congrArg (fun p : ClosedPoints g ↦ p.val.1) heq)
  · exact Subtype.ext (congrArg (fun p : ClosedPoints g ↦ p.val.1) heq)

theorem surjective_singularOrbit :
    Surjective (singularOrbit e g hg ρ hρ1 hi C hC hgen) := by
  rintro ⟨q, hq⟩
  obtain ⟨a, hdiag, rfl⟩ := hq
  rcases a with ⟨⟨x, y⟩, hcl⟩
  change x = y at hdiag
  subst y
  have hx : x ∈ closedBall 0 1 := (closure_subset_closedBall g hcl).1
  have hs := singular_of_diagonal_mem_closure e g hg ⟨(x, x), hcl⟩ rfl
  exact ⟨⟨x, hx, hs⟩, rfl⟩

def singularBoundaryEquiv : singularSet g ≃ diagonalOrbits g :=
  Equiv.ofBijective (singularOrbit e g hg ρ hρ1 hi C hC hgen)
    ⟨injective_singularOrbit e g hg ρ hρ1 hi C hC hgen,
      surjective_singularOrbit e g hg ρ hρ1 hi C hC hgen⟩

include e hg hρ1 hi hC hgen in
theorem singularBoundary_ncard : (singularSet g).ncard = (diagonalOrbits g).ncard := by
  simpa only [Nat.card_coe_set_eq] using
    Nat.card_congr (singularBoundaryEquiv e g hg ρ hρ1 hi C hC hgen)

end NoExoticSixSphere.DiskDoublePoints
