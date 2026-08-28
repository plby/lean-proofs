import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingData
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnitOrders
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorBasic

/-!
# Elliptic germs of the actual global canonical generator

The actual normalized elliptic chart preserves vanishing orders.  This
uses its proved local biholomorphism, together with the original open-disc
and upper-half-plane manifold charts.
-/

noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator

/-- The zero multiplicity of the homogeneous generator at an elliptic centre. -/
def ellipticExponent : Elliptic.Kind → ℕ
  | .three => 2
  | .four => 1

@[simp] theorem ellipticExponent_three : ellipticExponent .three = 2 := rfl

@[simp] theorem ellipticExponent_four : ellipticExponent .four = 1 := rfl

/-- The actual full-disc lift is a local biholomorphism into the original
upper half-plane, including the centre. -/
theorem neighborhoodLift_isLocalDiffeomorph (j : Elliptic.Kind) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (EllipticFilling.neighborhoodLift j) := by
  intro s
  exact ((Triangle.ellipticNeighborhoodChart j).symm.isLocalDiffeomorph s).comp
    (K := 𝓘(ℂ)) (P := ℍ)
    (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (Triangle.ellipticNeighborhood j)
      ((Triangle.ellipticNeighborhoodChart j).symm s))

private theorem upperHalfPlaneCoe_isLocalDiffeomorph (a : ℍ) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℍ → ℂ) a := by
  refine ⟨{
    toPartialEquiv := (chartAt ℂ a).toPartialEquiv
    open_source := (chartAt ℂ a).open_source
    open_target := (chartAt ℂ a).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }, mem_chart_source ℂ a, ?_⟩
  intro b hb
  rfl

private theorem discChart_symm_isLocalDiffeomorphAt :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ discZero).symm (0 : ℂ) := by
  refine ⟨{
    toPartialEquiv := (chartAt ℂ discZero).symm.toPartialEquiv
    open_source := (chartAt ℂ discZero).open_target
    open_target := (chartAt ℂ discZero).open_source
    contMDiffOn_toFun := contMDiffOn_chart_symm
    contMDiffOn_invFun := contMDiffOn_chart },
    SectionsUnit.zero_mem_discChart_target, Set.eqOn_refl _ _⟩

/-- The actual inverse normalized elliptic coordinate in ambient complex
coordinates, using the original open-disc chart at zero. -/
def discAmbientLift (j : Elliptic.Kind) (z : ℂ) : ℂ :=
  (EllipticFilling.neighborhoodLift j ((chartAt ℂ discZero).symm z) : ℂ)

@[simp] theorem discAmbientLift_zero (j : Elliptic.Kind) :
    discAmbientLift j 0 = (Triangle.ellipticCenter j : ℂ) := by
  simp only [discAmbientLift, SectionsUnit.discChart_symm_zero,
    EllipticFilling.neighborhoodLift_zero]

/-- The actual ambient coordinate change is locally biholomorphic at zero. -/
theorem discAmbientLift_isLocalDiffeomorphAt (j : Elliptic.Kind) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (discAmbientLift j) (0 : ℂ) :=
  (discChart_symm_isLocalDiffeomorphAt.comp (K := 𝓘(ℂ)) (P := ℍ)
    (neighborhoodLift_isLocalDiffeomorph j _)).comp (K := 𝓘(ℂ)) (P := ℂ)
    (upperHalfPlaneCoe_isLocalDiffeomorph _)

theorem discAmbientLift_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ (discAmbientLift j) 0 :=
  (discAmbientLift_isLocalDiffeomorphAt j).contMDiffAt.contDiffAt.analyticAt

theorem discAmbientLift_deriv_ne_zero (j : Elliptic.Kind) :
    deriv (discAmbientLift j) 0 ≠ 0 :=
  MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (discAmbientLift_isLocalDiffeomorphAt j)

/-- Changing from the actual upper-half-plane coordinate to the actual
normalized elliptic disc preserves the order, even for a nonanalytic germ. -/
theorem discExtension_neighborhoodLift_order (f : ℍ → ℂ) (j : Elliptic.Kind) :
    analyticOrderAt
        (SectionsUnit.discExtension (f ∘ EllipticFilling.neighborhoodLift j)) 0 =
      analyticOrderAt (f ∘ ofComplex) (Triangle.ellipticCenter j : ℂ) := by
  have he : SectionsUnit.discExtension (f ∘ EllipticFilling.neighborhoodLift j) =
      (f ∘ ofComplex) ∘ discAmbientLift j := by
    funext z
    simp only [SectionsUnit.discExtension, discAmbientLift, Function.comp_apply,
      ofComplex_apply]
  rw [he, analyticOrderAt_comp_of_deriv_ne_zero (discAmbientLift_analyticAt j)
    (discAmbientLift_deriv_ne_zero j), discAmbientLift_zero]

private theorem exists_unit_ball_of_order {f : ℂ → ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f 0) (horder : analyticOrderAt f 0 = (n : ℕ∞)) :
    ∃ (u : ℂ → ℂ) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
      AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, u z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, f z = z ^ n * u z) := by
  obtain ⟨u, hu, hu0, he⟩ := hf.analyticOrderAt_eq_natCast.mp horder
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ),
      AnalyticAt ℂ u z ∧ u z ≠ 0 ∧ f z = z ^ n * u z := by
    filter_upwards [hu.eventually_analyticAt, hu.continuousAt.eventually_ne hu0, he]
      with z haz hnz hez
    exact ⟨haz, hnz, by simpa only [sub_zero, smul_eq_mul] using hez⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨u, min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_, ?_, ?_⟩
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).1
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).2.1
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).2.2

/-- The global function evaluated in the actual normalized elliptic disc. -/
def discGenerator (j : Elliptic.Kind) (s : Disc) : ℂ :=
  generator (EllipticFilling.neighborhoodLift j s)

theorem discGenerator_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (discGenerator j) :=
  generator_holomorphic.comp (EllipticFilling.neighborhoodLift_holomorphic j)

theorem discGenerator_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ (SectionsUnit.discExtension (discGenerator j)) 0 :=
  SectionsUnit.discExtension_analyticAt (discGenerator_holomorphic j)

theorem generator_order_ellipticCenter (j : Elliptic.Kind) :
    analyticOrderAt (generator ∘ ofComplex) (Triangle.ellipticCenter j : ℂ) =
      (ellipticExponent j : ℕ∞) := by
  cases j
  · exact generator_order_centerOne
  · exact generator_order_centerTwo

/-- The source's exponents two and one are the orders in the actual
elliptic disc chart, not merely orders in an unrelated coordinate. -/
theorem discGenerator_order (j : Elliptic.Kind) :
    analyticOrderAt (SectionsUnit.discExtension (discGenerator j)) 0 =
      (ellipticExponent j : ℕ∞) :=
  (discExtension_neighborhoodLift_order generator j).trans
    (generator_order_ellipticCenter j)

theorem discGenerator_order_three :
    analyticOrderAt (SectionsUnit.discExtension (discGenerator .three)) 0 = 2 :=
  discGenerator_order .three

theorem discGenerator_order_four :
    analyticOrderAt (SectionsUnit.discExtension (discGenerator .four)) 0 = 1 :=
  discGenerator_order .four

/-- Dividing out the exact local zero leaves an analytic unit germ. -/
theorem exists_discGenerator_analytic_unit (j : Elliptic.Kind) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      SectionsUnit.discExtension (discGenerator j) =ᶠ[𝓝 (0 : ℂ)]
        fun z => z ^ ellipticExponent j * u z := by
  obtain ⟨u, hu, hu0, he⟩ :=
    (discGenerator_analyticAt j).analyticOrderAt_eq_natCast.mp (discGenerator_order j)
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [he] with z hz
  simpa only [sub_zero, smul_eq_mul] using hz

/-- The analytic unit germ is represented by an everywhere nonzero
analytic function on a genuine positive-radius ball inside the unit disc. -/
theorem exists_discGenerator_unit_ball (j : Elliptic.Kind) :
    ∃ (u : ℂ → ℂ) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
      AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, u z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r,
        SectionsUnit.discExtension (discGenerator j) z = z ^ ellipticExponent j * u z) :=
  exists_unit_ball_of_order (discGenerator_analyticAt j) (discGenerator_order j)

/-- A chosen analytic unit obtained by cancellation of the actual zero. -/
def ellipticUnit (j : Elliptic.Kind) : ℂ → ℂ :=
  (exists_discGenerator_unit_ball j).choose

/-- A proved positive radius on which cancellation gives an analytic unit. -/
def ellipticUnitRadius (j : Elliptic.Kind) : ℝ :=
  (exists_discGenerator_unit_ball j).choose_spec.choose

theorem ellipticUnitRadius_pos (j : Elliptic.Kind) : 0 < ellipticUnitRadius j :=
  (exists_discGenerator_unit_ball j).choose_spec.choose_spec.1

theorem ellipticUnitRadius_le_one (j : Elliptic.Kind) : ellipticUnitRadius j ≤ 1 :=
  (exists_discGenerator_unit_ball j).choose_spec.choose_spec.2.1

theorem ellipticUnit_analyticOnNhd (j : Elliptic.Kind) :
    AnalyticOnNhd ℂ (ellipticUnit j) (Metric.ball 0 (ellipticUnitRadius j)) :=
  (exists_discGenerator_unit_ball j).choose_spec.choose_spec.2.2.1

theorem ellipticUnit_ne_zero (j : Elliptic.Kind) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (ellipticUnitRadius j)) : ellipticUnit j z ≠ 0 :=
  (exists_discGenerator_unit_ball j).choose_spec.choose_spec.2.2.2.1 z hz

theorem ellipticUnit_analyticAt (j : Elliptic.Kind) : AnalyticAt ℂ (ellipticUnit j) 0 :=
  ellipticUnit_analyticOnNhd j 0 (Metric.mem_ball_self (ellipticUnitRadius_pos j))

theorem ellipticUnit_zero_ne_zero (j : Elliptic.Kind) : ellipticUnit j 0 ≠ 0 :=
  ellipticUnit_ne_zero j (Metric.mem_ball_self (ellipticUnitRadius_pos j))

theorem discGenerator_ambient_factor (j : Elliptic.Kind) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (ellipticUnitRadius j)) :
    SectionsUnit.discExtension (discGenerator j) z =
      z ^ ellipticExponent j * ellipticUnit j z :=
  (exists_discGenerator_unit_ball j).choose_spec.choose_spec.2.2.2.2 z hz

private theorem discExtension_coe (f : Disc → ℂ) (s : Disc) :
    SectionsUnit.discExtension f (s : ℂ) = f s := by
  change f ((chartAt ℂ discZero).symm ((chartAt ℂ discZero) s)) = f s
  rw [(chartAt ℂ discZero).left_inv (by trivial)]

/-- Exact factorization in the original disc, on the constructed ball. -/
theorem discGenerator_factor (j : Elliptic.Kind) (s : Disc)
    (hs : ‖(s : ℂ)‖ < ellipticUnitRadius j) :
    discGenerator j s = (s : ℂ) ^ ellipticExponent j * ellipticUnit j s := by
  have h := discGenerator_ambient_factor j (z := (s : ℂ))
    (by simpa only [Metric.mem_ball, dist_zero_right] using hs)
  simpa only [discExtension_coe] using h

/-- On the punctured disc, the analytic unit is the actual quotient by
the source's required elliptic power. -/
theorem discGenerator_div_power (j : Elliptic.Kind) (s : Disc)
    (hs : ‖(s : ℂ)‖ < ellipticUnitRadius j) (hs0 : (s : ℂ) ≠ 0) :
    discGenerator j s / (s : ℂ) ^ ellipticExponent j = ellipticUnit j s := by
  rw [discGenerator_factor j s hs, mul_div_cancel_left₀ _ (pow_ne_zero _ hs0)]

/-- The cancelling unit is holomorphic as a germ on the actual disc. -/
theorem ellipticUnit_native_holomorphicAt (j : Elliptic.Kind) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun s : Disc => ellipticUnit j s) discZero :=
  (ellipticUnit_analyticAt j).contDiffAt.contMDiffAt.comp discZero
    (contMDiff_subtype_val discZero)

/-- The factorization also holds as a germ of functions on the actual
open-disc manifold. -/
theorem discGenerator_factor_eventually (j : Elliptic.Kind) :
    discGenerator j =ᶠ[𝓝 discZero]
      fun s : Disc => (s : ℂ) ^ ellipticExponent j * ellipticUnit j s := by
  have hn : ∀ᶠ s : Disc in 𝓝 discZero, ‖(s : ℂ)‖ < ellipticUnitRadius j :=
    (continuous_subtype_val.norm.tendsto discZero).eventually
      (gt_mem_nhds (by simpa only [discZero_val, norm_zero] using ellipticUnitRadius_pos j))
  filter_upwards [hn] with s hs
  exact discGenerator_factor j s hs

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator
