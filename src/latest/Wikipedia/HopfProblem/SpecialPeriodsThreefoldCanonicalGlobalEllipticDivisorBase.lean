import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatchesOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationOrders

/-!
# The actual order-four elliptic support and its dense complement

The support is the literal fibre of the constructed sphere projection over
one, and the elliptic patch is the full inverse image used in the original
gluing.  Its complement is dense: every point of the support has a genuine
power-coordinate chart, and the dense set of model points with nonzero
first coordinate pulls back to points outside the support.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open Wikipedia.HopfProblem.Elliptic TrianglePeriodFamily.Canonical EllipticGeometry

attribute [local instance] Threefold.chartedSpace

/-- The entire original order-four elliptic patch in the glued threefold. -/
def patch : TopologicalSpace.Opens Threefold.Space :=
  Threefold.liftedPatch (some (some Kind.four))

/-- The actual reduced support of the order-four elliptic fibre. -/
def support : Set Threefold.Space :=
  Threefold.projectionSphere ⁻¹' {((1 : ℂ) : RiemannSphere)}

@[simp] theorem mem_support (x : Threefold.Space) :
    x ∈ support ↔ Threefold.projectionSphere x = ((1 : ℂ) : RiemannSphere) := Iff.rfl

theorem support_closed : IsClosed support :=
  isClosed_singleton.preimage Threefold.projectionSphere_continuous

/-- The actual open complement of the entire central sphere fibre. -/
def outside : TopologicalSpace.Opens Threefold.Space :=
  ⟨supportᶜ, support_closed.isOpen_compl⟩

@[simp] theorem outside_coe : (outside : Set Threefold.Space) = supportᶜ := rfl

@[simp] theorem mem_outside (x : Threefold.Space) :
    x ∈ outside ↔ Threefold.projectionSphere x ≠ ((1 : ℂ) : RiemannSphere) := Iff.rfl

/-- Every point of the literal central fibre lies in the full original elliptic patch. -/
theorem support_subset_patch : support ⊆ (patch : Set Threefold.Space) := by
  intro x hx
  exact FibreClassification.elliptic_fibre_mem_liftedPatch .four x
    ((mem_support x).mp hx |>.trans sphereValue_four.symm)

theorem mem_outside_or_patch (x : Threefold.Space) : x ∈ outside ∨ x ∈ patch := by
  by_cases hx : x ∈ support
  · exact Or.inr (support_subset_patch hx)
  · exact Or.inl hx

/-- The complement and the full elliptic patch cover the genuine global threefold. -/
theorem outside_union_patch :
    (outside : Set Threefold.Space) ∪ (patch : Set Threefold.Space) = univ :=
  eq_univ_iff_forall.mpr mem_outside_or_patch

/-- The complement of the first-coordinate hyperplane is dense in the actual model. -/
theorem model_first_ne_zero_dense : Dense {u : Model | u.1 ≠ 0} := by
  have hd := (dense_compl_singleton (0 : ℂ)).prod
    (dense_univ : Dense (univ : Set ComplexPlane₂))
  convert hd using 1
  ext u
  simp

/-- Density follows from the actual local power equations at every point
of the central fibre, with no density or analytic-set assumption. -/
theorem outside_dense : Dense (outside : Set Threefold.Space) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hxU⟩ := hne
  by_cases hx : x ∈ support
  · obtain ⟨e, hxs, _, _, hp⟩ := FibreClassification.elliptic_fibre_power_chart .four x
      ((mem_support x).mp hx |>.trans sphereValue_four.symm)
    have hV : IsOpen (e '' (e.source ∩ U)) :=
      e.toOpenPartialHomeomorph.isOpen_image_source_inter hU
    have hVne : (e '' (e.source ∩ U)).Nonempty :=
      ⟨e x, ⟨x, ⟨hxs, hxU⟩, rfl⟩⟩
    obtain ⟨u, huV, hunz⟩ :=
      model_first_ne_zero_dense.inter_open_nonempty (e '' (e.source ∩ U)) hV hVne
    obtain ⟨w, ⟨hws, hwU⟩, rfl⟩ := huV
    refine ⟨w, hwU, (mem_outside w).mpr ?_⟩
    intro hw
    have hpower := hp (e w) (e.map_source' hws)
    have he : e.symm (e w) = w := e.left_inv' hws
    rw [he, hw, ← sphereValue_four, sphereChart_value] at hpower
    exact (pow_ne_zero _ hunz) hpower.symm
  · exact ⟨x, hxU, hx⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor
