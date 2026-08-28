import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationUniquenessGauge

/-!
# An analytic bundle isomorphism from an actual gauge

An everywhere nonzero entire gauge with the positive-translation factor
relation descends to the actual diagonal orbit quotient.  The independently
proved quotient-to-core identification then gives an analytic isomorphism of
the original native line bundles.  Both total-space maps are proved analytic;
neither a bundle isomorphism nor an analytic inverse is assumed.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

variable {p : PeriodDomain} (F G : FactorOfAutomorphy p)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- The actual quotient map induced by multiplication by the gauge. -/
def gaugeQuotientMap (g : ComplexPlane₂ → ℂ)
    (hrel : ∀ l : p.lattice, ∀ z, g (z + l) * (F.factor l z : ℂ) =
      (G.factor l z : ℂ) * g z) : AssociatedSpace F → AssociatedSpace G :=
  Quotient.lift (fun u : ComplexPlane₂ × ℂ => associatedMap G (u.1, g u.1 * u.2)) (by
    intro u v huv
    have he : associatedMap F u = associatedMap F v := Quotient.sound huv
    obtain ⟨l, hz, hc⟩ := (associatedMap_eq_iff F u v).mp he
    apply (associatedMap_eq_iff G _ _).mpr
    refine ⟨l, hz, ?_⟩
    change (G.factor l v.1 : ℂ) * (g v.1 * v.2) = g u.1 * u.2
    rw [← hz, ← hc, ← mul_assoc, ← hrel l v.1, mul_assoc])

@[simp] theorem gaugeQuotientMap_associatedMap (g : ComplexPlane₂ → ℂ) (hrel)
    (z : ComplexPlane₂) (c : ℂ) :
    gaugeQuotientMap F G g hrel (associatedMap F (z, c)) =
      associatedMap G (z, g z * c) := rfl

@[simp] theorem gaugeQuotientMap_preserves_base (g : ComplexPlane₂ → ℂ) (hrel)
    (u : AssociatedSpace F) :
    projection G (gaugeQuotientMap F G g hrel u) = projection F u := by
  obtain ⟨⟨z, c⟩, rfl⟩ := associatedMap_surjective F u
  rfl

/-- Analyticity descends through the genuine covering quotient. -/
theorem gaugeQuotientMap_holomorphic (g : ComplexPlane₂ → ℂ) (hrel)
    (hg : ContDiff ℂ ω g) :
    letI := associatedChartedSpace F
    letI := associatedChartedSpace G
    ContMDiff IP IP ω (gaugeQuotientMap F G g hrel) := by
  let := associatedChartedSpace F
  let := associatedChartedSpace G
  let := diagonalAction F
  apply CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap F) IP ω
  have hm : ContDiff ℂ ω (fun u : ComplexPlane₂ × ℂ => (u.1, g u.1 * u.2)) :=
    contDiff_fst.prodMk ((hg.comp contDiff_fst).mul contDiff_snd)
  change ContMDiff IP IP ω
    (fun u : ComplexPlane₂ × ℂ => associatedMap G (u.1, g u.1 * u.2))
  exact (associatedMap_holomorphic G).comp hm.contMDiff

/-- The preferred scalar coordinates describe a map of the original fibres. -/
def gaugeTotalSpaceMap (g : ComplexPlane₂ → ℂ) :
    (Core.data F).core.TotalSpace → (Core.data G).core.TotalSpace :=
  fun u => ⟨u.proj, g (Core.lift p u.proj u.proj) * id (α := ℂ) u.2⟩

/-- The native map is precisely the transferred quotient map. -/
theorem gaugeTotalSpaceMap_eq (g : ComplexPlane₂ → ℂ) (hrel) :
    gaugeTotalSpaceMap F G g =
      Core.fromAssociated G ∘ gaugeQuotientMap F G g hrel ∘ Core.toAssociated F := by
  funext u
  apply Core.toAssociated_injective G
  rw [Function.comp_apply, Function.comp_apply, Core.toAssociated_fromAssociated]
  change associatedMap G (Core.lift p u.proj u.proj,
      g (Core.lift p u.proj u.proj) * id (α := ℂ) u.2) =
    gaugeQuotientMap F G g hrel
      (associatedMap F (Core.lift p u.proj u.proj, id (α := ℂ) u.2))
  rfl

theorem gaugeTotalSpaceMap_holomorphic (g : ComplexPlane₂ → ℂ)
    (hrel : ∀ l : p.lattice, ∀ z, g (z + l) * (F.factor l z : ℂ) =
      (G.factor l z : ℂ) * g z)
    (hg : ContDiff ℂ ω g) :
    ContMDiff ((IC).prod I₁) ((IC).prod I₁) ω (gaugeTotalSpaceMap F G g) := by
  let := associatedChartedSpace F
  let := associatedChartedSpace G
  rw [gaugeTotalSpaceMap_eq F G g hrel]
  exact (Core.fromAssociated_holomorphic G).comp
    ((gaugeQuotientMap_holomorphic F G g hrel hg).comp
      (Core.toAssociated_holomorphic F))

/-- The inverse factor relation follows algebraically from the original one. -/
theorem inverse_gauge_relation (g : ComplexPlane₂ → ℂ)
    (hne : ∀ z, g z ≠ 0)
    (hrel : ∀ l : p.lattice, ∀ z, g (z + l) * (F.factor l z : ℂ) =
      (G.factor l z : ℂ) * g z) (l : p.lattice) (z : ComplexPlane₂) :
    (g (z + l))⁻¹ * (G.factor l z : ℂ) = (F.factor l z : ℂ) * (g z)⁻¹ := by
  apply mul_left_cancel₀ (hne (z + l))
  calc
    g (z + l) * ((g (z + l))⁻¹ * (G.factor l z : ℂ)) = (G.factor l z : ℂ) := by
      rw [← mul_assoc, mul_inv_cancel₀ (hne (z + l)), one_mul]
    _ = ((G.factor l z : ℂ) * g z) * (g z)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (hne z), mul_one]
    _ = g (z + l) * ((F.factor l z : ℂ) * (g z)⁻¹) := by
      rw [← hrel l z, mul_assoc]

/-- Genuine complex-linear equivalences on the original native fibres. -/
def gaugeFiberEquiv (g : ComplexPlane₂ → ℂ) (hne : ∀ z, g z ≠ 0) (b : p.Torus) :
    (Core.data F).core.Fiber b ≃ₗ[ℂ] (Core.data G).core.Fiber b where
  toFun c := g (Core.lift p b b) * id (α := ℂ) c
  invFun c := (g (Core.lift p b b))⁻¹ * id (α := ℂ) c
  left_inv c := by
    change (g (Core.lift p b b))⁻¹ * (g (Core.lift p b b) * id (α := ℂ) c) =
      id (α := ℂ) c
    rw [← mul_assoc, inv_mul_cancel₀ (hne _), one_mul]
  right_inv c := by
    change g (Core.lift p b b) * ((g (Core.lift p b b))⁻¹ * id (α := ℂ) c) =
      id (α := ℂ) c
    rw [← mul_assoc, mul_inv_cancel₀ (hne _), one_mul]
  map_add' c d := mul_add _ (id (α := ℂ) c) (id (α := ℂ) d)
  map_smul' a c := mul_left_comm _ a (id (α := ℂ) c)

/-- A nonvanishing entire gauge induces an actual analytic, fibre-linear
isomorphism of the native bundles, with analytic inverse derived from `1/g`. -/
def gaugeBundleIso (g : ComplexPlane₂ → ℂ) (hg : ContDiff ℂ ω g)
    (hne : ∀ z, g z ≠ 0)
    (hrel : ∀ l : p.lattice, ∀ z, g (z + l) * (F.factor l z : ℂ) =
      (G.factor l z : ℂ) * g z) :
    AnalyticBundleIso IC (Core.data F).core.Fiber (Core.data G).core.Fiber :=
  AnalyticBundleIso.ofFiberEquiv (gaugeFiberEquiv F G g hne)
    (gaugeTotalSpaceMap_holomorphic F G g hrel hg)
    (gaugeTotalSpaceMap_holomorphic G F (fun z => (g z)⁻¹)
      (inverse_gauge_relation F G g hne hrel) (hg.inv hne))

@[simp] theorem gaugeBundleIso_apply (g : ComplexPlane₂ → ℂ) (hg) (hne) (hrel)
    (u : (Core.data F).core.TotalSpace) :
    (gaugeBundleIso F G g hg hne hrel).diffeomorph u = gaugeTotalSpaceMap F G g u := rfl

/-- On actual quotient representatives, the isomorphism multiplies by the
specified gauge with the original positive-translation convention. -/
theorem gaugeBundleIso_associatedMap (g : ComplexPlane₂ → ℂ) (hg) (hne) (hrel)
    (z : ComplexPlane₂) (c : ℂ) :
    Core.toAssociated G
      ((gaugeBundleIso F G g hg hne hrel).diffeomorph
        (Core.fromAssociated F (associatedMap F (z, c)))) =
      associatedMap G (z, g z * c) := by
  rw [gaugeBundleIso_apply, gaugeTotalSpaceMap_eq F G g hrel]
  simp only [Function.comp_apply, Core.toAssociated_fromAssociated,
    gaugeQuotientMap_associatedMap]

/-- The independently extracted gauge of the constructed native isomorphism
is the original entire function. -/
theorem gaugeBundleIso_gauge (g : ComplexPlane₂ → ℂ) (hg) (hne) (hrel) :
    PeriodTorusLineBundleClassificationUniqueness.gauge (gaugeBundleIso F G g hg hne hrel) =
      g := by
  funext z
  apply associatedMap_fibre_injective G z
  have he := PeriodTorusLineBundleClassificationUniqueness.quotientMap_gauge
    (gaugeBundleIso F G g hg hne hrel) z 1
  rw [PeriodTorusLineBundleClassificationUniqueness.quotientMap,
    gaugeBundleIso_associatedMap, mul_one, mul_one] at he
  exact he.symm

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
