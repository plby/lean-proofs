import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessCoordinates
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# The entire nonvanishing gauge of an actual analytic bundle isomorphism

An isomorphism here is a diffeomorphism of the original native total spaces
and is complex-linear on their actual fibres.  Its scalar function is
extracted from the image of `[z,1]`.  Holomorphicity, nonvanishing, and the
factor transformation law are conclusions, not fields of an isomorphism.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

variable {p : PeriodDomain} (F G : FactorOfAutomorphy p)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- Actual analytic fibre-linear isomorphisms between the native cocycle bundles. -/
abbrev BundleIso := AnalyticBundleIso IC (Core.data F).core.Fiber (Core.data G).core.Fiber

variable {F G}

/-- Transfer the actual native total-space map through the independently
proved bundle-to-quotient identifications. -/
def quotientMap (e : BundleIso F G) : AssociatedSpace F → AssociatedSpace G :=
  fun u => Core.toAssociated G (e.diffeomorph (Core.fromAssociated F u))

@[simp] theorem quotientMap_preserves_base (e : BundleIso F G) (u : AssociatedSpace F) :
    projection G (quotientMap e u) = projection F u := by
  simp only [quotientMap, Core.projection_toAssociated, e.preserves_base,
    Core.fromAssociated_proj]

theorem quotientMap_holomorphic (e : BundleIso F G) :
    letI := associatedChartedSpace F
    letI := associatedChartedSpace G
    ContMDiff IP IP ω (quotientMap e) := by
  let := associatedChartedSpace F
  let := associatedChartedSpace G
  exact (Core.toAssociated_holomorphic G).comp
    (e.diffeomorph.contMDiff.comp (Core.fromAssociated_holomorphic F))

/-- The actual fibre map, expressed in the two scalar coordinates based at `z`. -/
def scalarFiberEquiv (e : BundleIso F G) (z : ComplexPlane₂) : ℂ ≃ₗ[ℂ] ℂ :=
  ((coverFiberEquiv F z).trans (e.fiberEquiv (p.lattice.mkQ z))).trans
    (coverFiberEquiv G z).symm

theorem quotientMap_associatedMap (e : BundleIso F G) (z : ComplexPlane₂) (c : ℂ) :
    quotientMap e (associatedMap F (z, c)) =
      associatedMap G (z, scalarFiberEquiv e z c) := by
  rw [quotientMap, fromAssociated_map, e.map_fiber, toAssociated_fibre_coordinate]
  rfl

/-- Extracted from the actual image of the unit vector at each covering point. -/
def gauge (e : BundleIso F G) : ComplexPlane₂ → ℂ :=
  liftCoordinate G (fun z => quotientMap e (associatedMap F (z, 1)))
    (fun _ => (quotientMap_preserves_base e _).trans rfl)

theorem gauge_eq_scalarFiberEquiv (e : BundleIso F G) (z : ComplexPlane₂) :
    gauge e z = scalarFiberEquiv e z 1 := by
  apply associatedMap_fibre_injective G z
  dsimp only [gauge]
  rw [associatedMap_liftCoordinate, quotientMap_associatedMap]

/-- Holomorphicity follows from the original analytic bundle maps and the
proved local-cover scalar-coordinate theorem. -/
theorem gauge_contDiff (e : BundleIso F G) : ContDiff ℂ ω (gauge e) := by
  let := associatedChartedSpace F
  let := associatedChartedSpace G
  apply liftCoordinate_contDiff
  exact (quotientMap_holomorphic e).comp
    ((associatedMap_holomorphic F).comp (contDiff_id.prodMk contDiff_const).contMDiff)

theorem gauge_ne_zero (e : BundleIso F G) (z : ComplexPlane₂) : gauge e z ≠ 0 := by
  rw [gauge_eq_scalarFiberEquiv]
  exact (map_ne_zero_iff (scalarFiberEquiv e z) (scalarFiberEquiv e z).injective).mpr
    one_ne_zero

/-- The value on every vector is forced by fibre linearity of the original map. -/
theorem quotientMap_gauge (e : BundleIso F G) (z : ComplexPlane₂) (c : ℂ) :
    quotientMap e (associatedMap F (z, c)) = associatedMap G (z, gauge e z * c) := by
  rw [quotientMap_associatedMap, gauge_eq_scalarFiberEquiv]
  congr 2
  calc
    scalarFiberEquiv e z c = scalarFiberEquiv e z (c • (1 : ℂ)) := by simp
    _ = c • scalarFiberEquiv e z 1 := map_smul _ _ _
    _ = scalarFiberEquiv e z 1 * c := by rw [smul_eq_mul, mul_comm]

/-- The transformation law is a consequence of equality in the actual
diagonal quotient, with the original positive-translation convention. -/
theorem gauge_factor_relation (e : BundleIso F G) (l : p.lattice) (z : ComplexPlane₂) :
    gauge e (z + l) * (F.factor l z : ℂ) = (G.factor l z : ℂ) * gauge e z := by
  apply associatedMap_fibre_injective G (z + l)
  calc
    associatedMap G (z + l, gauge e (z + l) * (F.factor l z : ℂ)) =
        quotientMap e (associatedMap F (z + l, (F.factor l z : ℂ))) :=
      (quotientMap_gauge e (z + l) (F.factor l z : ℂ)).symm
    _ = quotientMap e (associatedMap F (z, 1)) := by
      congr 1
      simpa only [mul_one] using associatedMap_diagonal F l (z, 1)
    _ = associatedMap G (z, gauge e z) := by rw [quotientMap_gauge, mul_one]
    _ = associatedMap G (z + l, (G.factor l z : ℂ) * gauge e z) :=
      (associatedMap_diagonal G l (z, gauge e z)).symm

theorem gauge_automorphy (e : BundleIso F G) (l : p.lattice) (z : ComplexPlane₂) :
    gauge e (z + l) = (G.factor l z : ℂ) / (F.factor l z : ℂ) * gauge e z := by
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff (F.factor_ne_zero l z)).mpr (gauge_factor_relation e l z)

/-- An actual bundle isomorphism therefore produces the analytic,
everywhere nonzero gauge required by the factor comparison argument. -/
theorem exists_entire_nonvanishing_gauge (e : BundleIso F G) :
    ∃ g : ComplexPlane₂ → ℂ, ContDiff ℂ ω g ∧ (∀ z, g z ≠ 0) ∧
      (∀ l : p.lattice, ∀ z, g (z + l) =
        (G.factor l z : ℂ) / (F.factor l z : ℂ) * g z) ∧
      ∀ z c, quotientMap e (associatedMap F (z, c)) = associatedMap G (z, g z * c) :=
  ⟨gauge e, gauge_contDiff e, gauge_ne_zero e, gauge_automorphy e, quotientMap_gauge e⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniqueness
