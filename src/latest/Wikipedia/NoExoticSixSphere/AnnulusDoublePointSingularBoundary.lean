import Wikipedia.NoExoticSixSphere.AnnulusDoublePointBoundaryCurve

/-!
# Original annulus singularities are exactly the diagonal boundary orbits

Each intrinsic singularity gives its literal diagonal point in the actual
double-point closure. Passing to swap orbits does not identify distinct
singularities. Conversely every diagonal orbit comes from an intrinsic
singularity. This constructs the original sets' bijection, not merely an
abstract equality of cardinalities.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AnnulusDoublePoints

open GLOrthonormalization InvolutionQuotient SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

abbrev singularSet (g : Vector 4 → M) : Set (Vector 4) :=
  domain 3 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}

variable (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
  (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
  (hi : ∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
    Injective (fderiv ℝ (e.toFun ∘ g) x))
  (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
  (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
  (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
    (fun x ↦ fderiv ℝ (c ∘ g) x) {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source})

def singularOrbit (x : singularSet g) : diagonalOrbits g :=
  ⟨unorderedProj g ⟨(x.val, x.val), singular_diagonal_mem_closure
    e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen x.val x.property.1 x.property.2⟩,
    (mem_diagonalOrbits_iff g _).mpr rfl⟩

theorem injective_singularOrbit :
    Injective (singularOrbit e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen) := by
  intro a b he
  have heq := congrArg Subtype.val he
  rcases (proj_eq_iff (swapClosure g) (swapClosure_involutive g) _ _).mp heq with heq | heq
  · exact Subtype.ext (congrArg (fun v : ClosedPoints g ↦ v.val.1) heq)
  · exact Subtype.ext (congrArg (fun v : ClosedPoints g ↦ v.val.1) heq)

theorem surjective_singularOrbit :
    Surjective (singularOrbit e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen) := by
  rintro ⟨q, hq⟩
  obtain ⟨a, hdiag, rfl⟩ := hq
  rcases a with ⟨⟨x, y⟩, hcl⟩
  change x = y at hdiag
  subst y
  have hx : x ∈ domain 3 := (closure_subset_domain g hcl).1
  have hs := singular_of_diagonal_mem_closure e g hg ⟨(x, x), hcl⟩ rfl
  exact ⟨⟨x, hx, hs⟩, rfl⟩

def singularBoundaryEquiv : singularSet g ≃ diagonalOrbits g :=
  Equiv.ofBijective (singularOrbit e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen)
    ⟨injective_singularOrbit e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen,
      surjective_singularOrbit e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen⟩

include e hg hr₀ hr₁ hi hC hgen in
theorem singularBoundary_ncard : (singularSet g).ncard = (diagonalOrbits g).ncard := by
  simpa only [Nat.card_coe_set_eq] using
    Nat.card_congr (singularBoundaryEquiv e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen)

end NoExoticSixSphere.AnnulusDoublePoints
