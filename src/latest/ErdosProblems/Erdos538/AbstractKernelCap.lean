import ErdosProblems.Erdos538.IsotropicKernel

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

/-- Abstract cap-two mechanism for the safe isotropic-kernel palette.  In a
common two-dimensional relation space on a parent, every selected facet gives
an isotropic vector whose unique zero coordinate is the omitted parent point.
If the restricted form is not totally isotropic, there are at most two such
facets. -/
theorem uniqueZeroIsotropic_selected_card_le_two
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq ι]
    (B : LinearMap.BilinForm K V) (hsym : B.IsSymm)
    (coord : ι → V →ₗ[K] K)
    (selected : Finset ι) (rel : ι → V)
    (hzero : ∀ x ∈ selected, coord x (rel x) = 0)
    (hfull : ∀ x ∈ selected, ∀ y, y ≠ x → coord y (rel x) ≠ 0)
    (hiso : ∀ x ∈ selected, B (rel x) (rel x) = 0)
    (hfin : Module.finrank K V = 2) (htwo : (2 : K) ≠ 0)
    (hnontotal : ¬ ∀ u v : V, B u v = 0) :
    selected.card ≤ 2 := by
  by_contra hcard
  have hthree : 2 < selected.card := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  have htotal := finrank_two_total_zero_of_three_unique_zero_vectors
    B hsym coord (rel x) (rel y) (rel z) x y z hxy hxz hyz
    (hzero x hx) (hzero y hy)
    (hfull x hx) (hfull y hy) (hfull z hz)
    hfin htwo (hiso x hx) (hiso y hy) (hiso z hz)
  exact hnontotal htotal

end Erdos538.IsotropicKernel
