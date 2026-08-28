import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalPrescribedDivisor
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry

/-!
# The actual finite domain covered by the regular and order-three patches

The prescribed Cartier divisor's generic set removes exactly the cusp
fibre and the order-four elliptic fibre.  It is the union of the actual
regular locus and the whole original order-three filling patch.  Its
intersection with the order-four patch is entirely regular.  These are
set identities for the already constructed global threefold and patches.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalFiniteRegularSection

open Triangle

attribute [local instance] Threefold.chartedSpace

/-- The actual complement of the prescribed divisor's zero and pole support. -/
def domain : Opens Threefold.Space := GlobalPrescribedDivisor.cartier.genericSet

@[simp] theorem mem_domain (x : Threefold.Space) :
    x ∈ domain ↔ Threefold.projectionSphere x ≠ (∞ : RiemannSphere) ∧
      Threefold.projectionSphere x ≠ ((1 : ℂ) : RiemannSphere) :=
  GlobalPrescribedDivisor.mem_genericSet x

/-- The same domain in the original compact triangle-base coordinates. -/
theorem mem_domain_iff_projection (x : Threefold.Space) :
    x ∈ domain ↔ Threefold.projection x ≠ Threefold.puncturePoint none ∧
      Threefold.projection x ≠ Threefold.puncturePoint (some Elliptic.Kind.four) := by
  rw [mem_domain]
  have hc : triangleSphereUniformization (Threefold.puncturePoint none) =
      (∞ : RiemannSphere) := triangleSphereUniformization_cusp
  have h₄ : triangleSphereUniformization
      (Threefold.puncturePoint (some Elliptic.Kind.four)) = ((1 : ℂ) : RiemannSphere) :=
    triangleSphereUniformization_centerTwo
  rw [← hc, ← h₄]
  change (triangleSphereUniformization (Threefold.projection x) ≠
      triangleSphereUniformization (Threefold.puncturePoint none) ∧
    triangleSphereUniformization (Threefold.projection x) ≠
      triangleSphereUniformization (Threefold.puncturePoint (some Elliptic.Kind.four))) ↔ _
  constructor
  · intro h
    exact ⟨fun he => h.1 (congrArg triangleSphereUniformization he),
      fun he => h.2 (congrArg triangleSphereUniformization he)⟩
  · intro h
    exact ⟨fun he => h.1 (triangleSphereUniformization.injective he),
      fun he => h.2 (triangleSphereUniformization.injective he)⟩

theorem regularLocus_le_domain : Threefold.regularLocus ≤ domain := by
  intro x hx
  have h := (Threefold.mem_regularPatch_iff_ne_puncture (Threefold.projection x)).mp hx
  exact (mem_domain_iff_projection x).mpr ⟨h none, h (some .four)⟩

/-- The whole order-three filling patch excludes both removed fibres. -/
theorem threePatch_le_domain :
    Threefold.liftedPatch (some (some Elliptic.Kind.three)) ≤ domain := by
  intro x hx
  have hp : Threefold.projection x ∈ specialBaseCover.fillingPatch (some .three) := hx
  apply (mem_domain_iff_projection x).mpr
  constructor
  · intro he
    have hbad := (specialBaseCover.point_mem_fillingPatch_iff none (some .three)).mp (he ▸ hp)
    cases hbad
  · intro he
    have hbad :=
      (specialBaseCover.point_mem_fillingPatch_iff (some .four) (some .three)).mp (he ▸ hp)
    cases hbad

/-- The only nonregular points retained in the finite domain lie over zero. -/
theorem projectionSphere_eq_zero_of_mem_domain_not_mem_regular {x : Threefold.Space}
    (hx : x ∈ domain) (hr : x ∉ Threefold.regularLocus) :
    Threefold.projectionSphere x = ((0 : ℂ) : RiemannSphere) := by
  classical
  by_contra hz
  have hd := (mem_domain x).mp hx
  exact hr ((Threefold.mem_regularLocus_iff_sphere x).mpr
    ((Threefold.mem_sphereRegularPatch _).mpr ⟨hd.1, hz, hd.2⟩))

/-- Every such point belongs to the actual full order-three filling patch. -/
theorem mem_threePatch_of_mem_domain_not_mem_regular {x : Threefold.Space}
    (hx : x ∈ domain) (hr : x ∉ Threefold.regularLocus) :
    x ∈ Threefold.liftedPatch (some (some Elliptic.Kind.three)) :=
  FibreClassification.elliptic_fibre_mem_liftedPatch .three x
    ((projectionSphere_eq_zero_of_mem_domain_not_mem_regular hx hr).trans
      EllipticGeometry.sphereValue_three.symm)

theorem mem_regular_or_threePatch_of_mem_domain {x : Threefold.Space} (hx : x ∈ domain) :
    x ∈ Threefold.regularLocus ∨
      x ∈ Threefold.liftedPatch (some (some Elliptic.Kind.three)) := by
  classical
  by_cases hr : x ∈ Threefold.regularLocus
  · exact Or.inl hr
  · exact Or.inr (mem_threePatch_of_mem_domain_not_mem_regular hx hr)

theorem mem_domain_iff_regular_or_threePatch (x : Threefold.Space) :
    x ∈ domain ↔ x ∈ Threefold.regularLocus ∨
      x ∈ Threefold.liftedPatch (some (some Elliptic.Kind.three)) :=
  ⟨mem_regular_or_threePatch_of_mem_domain,
    fun h => h.elim (fun hr => regularLocus_le_domain hr) (fun h₃ => threePatch_le_domain h₃)⟩

/-- These two original open patches cover exactly the entire generic domain. -/
theorem domain_eq_regular_sup_threePatch :
    domain = Threefold.regularLocus ⊔
      Threefold.liftedPatch (some (some Elliptic.Kind.three)) := by
  apply le_antisymm
  · intro x hx
    exact Opens.mem_sup.mpr (mem_regular_or_threePatch_of_mem_domain hx)
  · exact sup_le regularLocus_le_domain threePatch_le_domain

theorem domain_inf_threePatch_eq :
    domain ⊓ Threefold.liftedPatch (some (some Elliptic.Kind.three)) =
      Threefold.liftedPatch (some (some Elliptic.Kind.three)) :=
  inf_eq_right.mpr threePatch_le_domain

/-- In the order-four patch, deleting its central fibre leaves only regular points. -/
theorem domain_inf_fourPatch_le_regularLocus :
    domain ⊓ Threefold.liftedPatch (some (some Elliptic.Kind.four)) ≤
      Threefold.regularLocus := by
  intro x hx
  change Threefold.projection x ∈ Threefold.regularPatch
  exact (specialBaseCover.fillingPatch_regular_iff (some .four) hx.2).mpr
    ((mem_domain_iff_projection x).mp hx.1).2

theorem mem_regular_of_mem_domain_of_mem_fourPatch {x : Threefold.Space}
    (hx : x ∈ domain)
    (h₄ : x ∈ Threefold.liftedPatch (some (some Elliptic.Kind.four))) :
    x ∈ Threefold.regularLocus :=
  domain_inf_fourPatch_le_regularLocus ⟨hx, h₄⟩

/-- The exact overlap with the original order-four patch is its regular part. -/
theorem domain_inf_fourPatch_eq :
    domain ⊓ Threefold.liftedPatch (some (some Elliptic.Kind.four)) =
      Threefold.regularLocus ⊓ Threefold.liftedPatch (some (some Elliptic.Kind.four)) := by
  apply le_antisymm
  · intro x hx
    exact ⟨domain_inf_fourPatch_le_regularLocus hx, hx.2⟩
  · intro x hx
    exact ⟨regularLocus_le_domain hx.1, hx.2⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalFiniteRegularSection
