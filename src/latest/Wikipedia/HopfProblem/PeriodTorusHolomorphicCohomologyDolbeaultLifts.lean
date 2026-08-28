import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGeometry
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCalculusLocal

/-!
# Actual periodic lifts of native smooth torus sections

A section is pulled back along the original quotient projection. Its
lift is genuinely smooth above its domain and is literally lattice
periodic. The actual antiholomorphic coordinate derivatives agree at
different lifts of every point in that domain, by translation calculus.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationHolomorphicFrame

/-- The literal inverse image of a native torus open under the period projection. -/
def coverOpen (p : PeriodDomain) (U : Opens p.Torus) : Opens ComplexPlane₂ :=
  ⟨p.lattice.mkQ ⁻¹' U, U.isOpen.preimage p.lattice.continuous_mkQ⟩

/-- The actual lifted function, with zero extension used only outside its domain. -/
def liftSection (p : PeriodDomain) (U : Opens p.Torus) (s : SmoothSection p U) :
    ComplexPlane₂ → ℂ := smoothExtend p U s ∘ p.lattice.mkQ

@[simp] theorem liftSection_apply (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    liftSection p U s z = s ⟨p.lattice.mkQ z, hz⟩ :=
  smoothExtend_apply p U s (p.lattice.mkQ z) hz

/-- The actual lift is smooth above every point of the original open domain. -/
theorem liftSection_contDiffAt (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) (z : ComplexPlane₂) (hz : p.lattice.mkQ z ∈ U) :
    ContDiffAt ℝ ∞ (liftSection p U s) z :=
  ((smoothExtend_contMDiffAt p U s (p.lattice.mkQ z) hz).comp z
    (mkQ_contMDiff_real p z)).contDiffAt

theorem liftSection_contDiffOn (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) : ContDiffOn ℝ ∞ (liftSection p U s) (coverOpen p U) :=
  fun z hz => (liftSection_contDiffAt p U s z hz).contDiffWithinAt

/-- Lattice periodicity is literal because the lift factors through the actual quotient. -/
theorem liftSection_periodic (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) (z : ComplexPlane₂) (l : p.lattice) :
    liftSection p U s (z + l) = liftSection p U s z := by
  have hl : p.lattice.mkQ (l : ComplexPlane₂) = 0 :=
    (Submodule.Quotient.mk_eq_zero p.lattice).mpr l.property
  simp only [liftSection, Function.comp_apply, map_add, hl, add_zero]

theorem liftSection_add (p : PeriodDomain) (U : Opens p.Torus)
    (s t : SmoothSection p U) :
    liftSection p U (s + t) = fun z => liftSection p U s z + liftSection p U t z := by
  rw [liftSection, smoothExtend_add]
  rfl

theorem liftSection_smul (p : PeriodDomain) (U : Opens p.Torus)
    (c : ℂ) (s : SmoothSection p U) :
    liftSection p U (c • s) = fun z => c * liftSection p U s z := by
  rw [liftSection, smoothExtend_smul]
  rfl

/-- Restriction retains the same actual lifted germ at every point above the smaller open. -/
theorem liftSection_restrict_germ (p : PeriodDomain) {U V : Opens p.Torus}
    (h : U ≤ V) (s : SmoothSection p V) (z : ComplexPlane₂)
    (hz : p.lattice.mkQ z ∈ U) :
    liftSection p U (restriction p h s) =ᶠ[𝓝 z] liftSection p V s := by
  filter_upwards [(coverOpen p U).isOpen.mem_nhds hz] with w hw
  rw [liftSection_apply _ _ _ w hw, liftSection_apply _ _ _ w (h hw)]
  rfl

/-- The genuine coordinate derivative does not depend on the chosen lift
of a point of the actual open domain. -/
theorem dbar_lift_eq_of_mkQ_eq (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s : SmoothSection p U) {z w : ComplexPlane₂} (hz : p.lattice.mkQ z ∈ U)
    (he : p.lattice.mkQ z = p.lattice.mkQ w) :
    dbarCoordinate (liftSection p U s) i z = dbarCoordinate (liftSection p U s) i w := by
  let l : p.lattice := ⟨z - w, (Submodule.Quotient.eq p.lattice).mp he⟩
  have hwz : w + (l : ComplexPlane₂) = z := by
    dsimp [l]
    abel
  have hf : DifferentiableAt ℝ (liftSection p U s) (w + (l : ComplexPlane₂)) := by
    rw [hwz]
    exact (liftSection_contDiffAt p U s z hz).differentiableAt (by simp)
  have hp : (fun y => liftSection p U s (y + (l : ComplexPlane₂))) =
      liftSection p U s :=
    funext fun y => liftSection_periodic p U s y l
  have hd := dbarCoordinate_translate (z := w) (a := (l : ComplexPlane₂)) hf i
  rw [hp] at hd
  simpa only [hwz] using hd.symm

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
