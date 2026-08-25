import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportTransport.Defs
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Normals

/-! Finiteness and cardinality bounds for supporting normals in complex coordinates. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open FaceBounds

theorem complexSupportingNormalsAtLeast_eq_preimage (K : Set Plane) (δ : ℝ) :
    complexSupportingNormalsAtLeast K δ =
      Complex.equivRealProd ⁻¹' supportingNormalsAtLeast K δ := rfl

theorem equivRealProd_image_complexSupportingNormalsAtLeast (K : Set Plane) (δ : ℝ) :
    Complex.equivRealProd '' complexSupportingNormalsAtLeast K δ =
      supportingNormalsAtLeast K δ :=
  Complex.equivRealProd.image_preimage _

/-- Passing from coordinate pairs to complex numbers preserves finiteness. -/
theorem complexSupportingNormalsAtLeast_finite_iff (K : Set Plane) (δ : ℝ) :
    (complexSupportingNormalsAtLeast K δ).Finite ↔
      (supportingNormalsAtLeast K δ).Finite := by
  rw [complexSupportingNormalsAtLeast_eq_preimage]
  exact ⟨fun h => h.of_preimage Complex.equivRealProd.surjective,
    fun h => h.preimage Complex.equivRealProd.injective.injOn⟩

/-- Passing from coordinate pairs to complex numbers preserves cardinality. -/
theorem complexSupportingNormalsAtLeast_ncard (K : Set Plane) (δ : ℝ) :
    (complexSupportingNormalsAtLeast K δ).ncard =
      (supportingNormalsAtLeast K δ).ncard := by
  rw [complexSupportingNormalsAtLeast_eq_preimage]
  exact Set.ncard_preimage_of_injective_subset_range
    Complex.equivRealProd.injective (fun z _ => Complex.equivRealProd.surjective z)

/-- A positive lower bound on the supporting-segment lengths makes the complex
normal set finite for a convex set contained in a bounded rectangle. -/
theorem complexSupportingNormalsAtLeast_finite {K : Set Plane} (hK : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ) {l r bottom top : ℝ}
    (hlr : l ≤ r) (hbt : bottom ≤ top)
    (hbox : ∀ p ∈ K,
      (l ≤ p 0 ∧ p 0 ≤ r) ∧ (bottom ≤ p 1 ∧ p 1 ≤ top)) :
    (complexSupportingNormalsAtLeast K δ).Finite :=
  (complexSupportingNormalsAtLeast_finite_iff K δ).2
    (supportingNormalsAtLeast_finite hK hδ hlr hbt hbox)

/-- Unit supporting segments in a strict-height substrip of the square have
at most three complex outward unit normals. -/
theorem complexUnitSupportingNormals_finite_and_ncard_le_three {K : Set Plane}
    (hK : Convex ℝ K) (hSquare : K ⊆ unitSquare)
    {l h : ℝ} (hlh : l ≤ h) (hheight : h - l < 1)
    (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ h) :
    (complexUnitSupportingNormals K).Finite ∧
      (complexUnitSupportingNormals K).ncard ≤ 3 := by
  obtain ⟨hfinite, hcard⟩ :=
    unitSupportingNormals_finite_and_ncard_le_three hK hSquare hlh hheight hstrip
  refine ⟨(complexSupportingNormalsAtLeast_finite_iff K 1).2 hfinite, ?_⟩
  change (complexSupportingNormalsAtLeast K 1).ncard ≤ 3
  rw [complexSupportingNormalsAtLeast_ncard]
  exact hcard

/-- A finset presentation of all the complex unit supporting normals, retaining
the bound needed for the finite rotation-and-reflection argument. -/
theorem exists_finset_complexUnitSupportingNormals {K : Set Plane}
    (hK : Convex ℝ K) (hSquare : K ⊆ unitSquare)
    {l h : ℝ} (hlh : l ≤ h) (hheight : h - l < 1)
    (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ h) :
    ∃ s : Finset ℂ, (s : Set ℂ) = complexUnitSupportingNormals K ∧ s.card ≤ 3 := by
  classical
  obtain ⟨hfinite, hcard⟩ :=
    complexUnitSupportingNormals_finite_and_ncard_le_three hK hSquare hlh hheight hstrip
  refine ⟨hfinite.toFinset, hfinite.coe_toFinset, ?_⟩
  rwa [Set.ncard_eq_toFinset_card _ hfinite] at hcard

/-- A real normal would require a vertical unit supporting segment, which does
not fit in a strip of height strictly less than one. -/
theorem not_mem_complexUnitSupportingNormals_of_im_eq_zero {K : Set Plane}
    {z : ℂ} {l h : ℝ} (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ h)
    (hheight : h - l < 1) (him : z.im = 0) :
    z ∉ complexUnitSupportingNormals K :=
  not_mem_unitSupportingNormals_of_snd_eq_zero hstrip hheight him

theorem im_ne_zero_of_mem_complexUnitSupportingNormals {K : Set Plane}
    {z : ℂ} {l h : ℝ} (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ h)
    (hheight : h - l < 1) (hz : z ∈ complexUnitSupportingNormals K) :
    z.im ≠ 0 := by
  intro him
  exact not_mem_complexUnitSupportingNormals_of_im_eq_zero hstrip hheight him hz

end Puzzling139335.N4MiddleInvolutions.Reflection
