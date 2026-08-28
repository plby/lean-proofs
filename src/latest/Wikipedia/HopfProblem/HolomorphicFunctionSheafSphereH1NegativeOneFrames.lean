import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFramesFinite
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFramesInfinity
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheaf

/-!
# The genuine local frames and transition of the ideal sheaf O(-infinity)

The finite and reciprocal chart opens cover the actual Riemann sphere.
On every subopen set of either chart, multiplication by the corresponding
frame is a module isomorphism from actual holomorphic functions onto the
actual vanishing ideal, natural for literal restrictions.  Thus this is
sheaf-local rank-one freeness, not just an isomorphism of sections on two
large open sets.

The frame at infinity is the reciprocal coordinate.  On the overlap its
transition from the finite constant-one frame is the actual holomorphic
unit with finite-coordinate value `z⁻¹`.  These proved local frames and
transition identify the ideal sheaf as the usual O(-1).
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

open RiemannSphere

/-- The actual overlap of the two affine opens. -/
abbrev chartOverlap : Opens RiemannSphere := finiteChart ⊓ infinityChart

/-- The holomorphic transition coefficient on the actual overlap. -/
def transitionCoefficient :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere chartOverlap :=
  (infinityFrame chartOverlap inf_le_right).val

/-- Its actual holomorphic inverse is the finite coordinate. -/
def inverseTransitionCoefficient :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere chartOverlap :=
  fromFiniteSection chartOverlap id 0 (fun _ _ => analyticAt_id)
    (fun h => (infty_not_mem_finiteChart h.1).elim)

@[simp] theorem transitionCoefficient_coe (z : ℂ)
    (hz : (z : RiemannSphere) ∈ chartOverlap) :
    transitionCoefficient ⟨(z : RiemannSphere), hz⟩ = z⁻¹ := rfl

@[simp] theorem inverseTransitionCoefficient_coe (z : ℂ)
    (hz : (z : RiemannSphere) ∈ chartOverlap) :
    inverseTransitionCoefficient ⟨(z : RiemannSphere), hz⟩ = z := rfl

theorem transitionCoefficient_mul_inverse :
    transitionCoefficient * inverseTransitionCoefficient = 1 := by
  apply ContMDiffMap.ext
  rintro ⟨p, hp⟩
  induction p using OnePoint.rec with
  | infty => exact (infty_not_mem_finiteChart hp.1).elim
  | coe z =>
    change z⁻¹ * z = 1
    exact inv_mul_cancel₀ ((coe_mem_infinityChart_iff z).mp hp.2)

/-- The transition is a unit in the actual ring of holomorphic overlap sections. -/
def transitionUnit :
    (HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere chartOverlap)ˣ where
  val := transitionCoefficient
  inv := inverseTransitionCoefficient
  val_inv := transitionCoefficient_mul_inverse
  inv_val := by rw [mul_comm]; exact transitionCoefficient_mul_inverse

@[simp] theorem transitionUnit_coe (z : ℂ) (hz : (z : RiemannSphere) ∈ chartOverlap) :
    (transitionUnit : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere chartOverlap)
      ⟨(z : RiemannSphere), hz⟩ = z⁻¹ := rfl

@[simp] theorem transitionUnit_inv_coe (z : ℂ) (hz : (z : RiemannSphere) ∈ chartOverlap) :
    (↑(transitionUnit⁻¹) : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere chartOverlap)
      ⟨(z : RiemannSphere), hz⟩ = z := rfl

/-- The actual restricted frames have the usual O(-1) transition. -/
theorem frame_transition :
    negativeOneRestriction (show chartOverlap ≤ infinityChart from inf_le_right)
        (infinityFrame infinityChart le_rfl) =
      (transitionUnit : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere chartOverlap) •
        negativeOneRestriction (show chartOverlap ≤ finiteChart from inf_le_left)
          (finiteFrame finiteChart le_rfl) := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  change fromFinite (fun z : ℂ => z⁻¹) 0 p = fromFinite (fun z : ℂ => z⁻¹) 0 p * 1
  exact (mul_one _).symm

/-- The reverse change of frame uses the proved inverse holomorphic unit. -/
theorem frame_transition_inverse :
    negativeOneRestriction (show chartOverlap ≤ finiteChart from inf_le_left)
        (finiteFrame finiteChart le_rfl) =
      (↑(transitionUnit⁻¹) : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere chartOverlap) •
        negativeOneRestriction (show chartOverlap ≤ infinityChart from inf_le_right)
          (infinityFrame infinityChart le_rfl) := by
  rw [frame_transition, ← mul_smul]
  simp

/-- In the finite coordinate, the infinity frame is `z⁻¹` times the finite frame. -/
theorem frame_transition_finite_coordinate (z : ℂ) (hz : z ≠ 0) :
    (infinityFrame infinityChart le_rfl).val
        ⟨(z : RiemannSphere), (coe_mem_infinityChart_iff z).mpr hz⟩ =
      z⁻¹ * (finiteFrame finiteChart le_rfl).val
        ⟨(z : RiemannSphere), coe_mem_finiteChart z⟩ := by
  change z⁻¹ = z⁻¹ * 1
  exact (mul_one _).symm

/-- In reciprocal coordinate `u`, the finite frame is `u⁻¹` times the infinity frame. -/
theorem frame_transition_reciprocal_coordinate (u : ℂ) (hu : u ≠ 0) :
    (finiteFrame finiteChart le_rfl).val
        ⟨infinityParametrization u, (infinityParametrization_mem_finiteChart_iff u).mpr hu⟩ =
      u⁻¹ * (infinityFrame infinityChart le_rfl).val
        ⟨infinityParametrization u, infinityParametrization_mem u⟩ := by
  change 1 = u⁻¹ * (infinityFrame infinityChart le_rfl).val _
  rw [infinityFrame_parametrization]
  exact (inv_mul_cancel₀ hu).symm

/-- The two actual opens carrying the local frames. -/
def frameChart : Bool → Opens RiemannSphere
  | false => finiteChart
  | true => infinityChart

theorem frameChart_cover (p : RiemannSphere) : ∃ b : Bool, p ∈ frameChart b := by
  obtain h | h := chart_cover p
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- The frame family on all subopens of each member of the actual cover. -/
def chartFrame (b : Bool) (U : Opens RiemannSphere) (hU : U ≤ frameChart b) :
    NegativeOneSection U := by
  cases b
  · exact finiteFrame U hU
  · exact infinityFrame U hU

/-- The actual rank-one module identification on every chart subopen. -/
def chartTrivialization (b : Bool) (U : Opens RiemannSphere) (hU : U ≤ frameChart b) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U ≃ₗ[
      HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U] NegativeOneSection U := by
  cases b
  · exact finiteTrivialization U hU
  · exact infinityTrivialization U hU

theorem chartTrivialization_as_frame (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ frameChart b) (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    chartTrivialization b U hU f = f • chartFrame b U hU := by
  cases b
  · exact finiteTrivialization_as_frame U hU f
  · rfl

/-- These are natural identifications of the sheaf section modules,
not independent equivalences on selected large open sets. -/
theorem chartTrivialization_restrict (b : Bool) {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ frameChart b) (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere V) :
    negativeOneRestriction h (chartTrivialization b V hV f) =
      chartTrivialization b U (h.trans hV)
        (ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h f) := by
  cases b
  · exact finiteTrivialization_restrict h hV f
  · exact infinityTrivialization_restrict h hV f

/-- At every actual sphere point, all smaller opens in a genuine chart
have free rank-one ideal-section modules, with the natural frame maps above. -/
theorem locally_free_rank_one (p : RiemannSphere) :
    ∃ b : Bool, p ∈ frameChart b ∧ ∀ (U : Opens RiemannSphere) (_hU : U ≤ frameChart b),
      Nonempty (HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U ≃ₗ[
        HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U] NegativeOneSection U) := by
  obtain ⟨b, hb⟩ := frameChart_cover p
  exact ⟨b, hb, fun U hU => ⟨chartTrivialization b U hU⟩⟩

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames
