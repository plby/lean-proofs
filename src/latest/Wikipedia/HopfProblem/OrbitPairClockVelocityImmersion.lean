import Wikipedia.SmoothSixDPoincare.WeightedDerivativePerturbation
import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints

/-!
# Full projected immersion along a curve by a common time velocity

In a vector target, adding `κ(t) • a` to every point of a time slice
preserves its complete collision set. Along a low-dimensional locus where
the clock derivative is nonzero, arbitrarily small common velocities make
the full time-space map immersive, provided the old spatial derivatives
are injective. The dimension condition is `1 + 3 < 5` for a curve in a
surface family with five-dimensional target.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.ClockVelocity

open Wikipedia.SmoothSixDPoincare

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def perturb (f : ℝ × E → G) (κ : ℝ → ℝ) (a : G) (q : ℝ × E) : G :=
  f q + κ q.1 • a

theorem perturb_fixed_time (f : ℝ × E → G) (κ : ℝ → ℝ) (a : G) {t : ℝ}
    (ht : κ t = 0) (x : E) : perturb f κ a (t, x) = f (t, x) := by
  simp [perturb, ht]

theorem spatial_derivative_perturb (f : ℝ × E → G) (κ : ℝ → ℝ) (a : G)
    (t : ℝ) (x : E) :
    fderiv ℝ (fun y => perturb f κ a (t, y)) x =
      fderiv ℝ (fun y => f (t, y)) x :=
  fderiv_add_const (κ t • a)

theorem doublePoints_perturb (f : ℝ × E → G) (κ : ℝ → ℝ) (a : G) :
    FamilyDoublePoints.doublePoints (perturb f κ a) = FamilyDoublePoints.doublePoints f := by
  ext q
  change (q.2.1 ≠ q.2.2 ∧ f (q.1, q.2.1) + κ q.1 • a =
      f (q.1, q.2.2) + κ q.1 • a) ↔
    (q.2.1 ≠ q.2.2 ∧ f (q.1, q.2.1) = f (q.1, q.2.2))
  exact and_congr_right (fun _ => add_left_inj _)

theorem common_kernel_zero {f : ℝ × E → G} {κ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hκ : ContDiff ℝ ∞ κ) (q : ℝ × E)
    (hi : Injective (fderiv ℝ (fun x => f (q.1, x)) q.2))
    (hκne : deriv κ q.1 ≠ 0) (v : ℝ × E)
    (hfzero : fderiv ℝ f q v = 0)
    (hκzero : fderiv ℝ (fun p : ℝ × E => κ p.1) q v = 0) : v = 0 := by
  have hd : HasFDerivAt (fun p : ℝ × E => κ p.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv κ q.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ E)) q :=
    ((hκ.differentiable (by simp) q.1).hasDerivAt.hasFDerivAt).comp q hasFDerivAt_fst
  have hclock : v.1 * deriv κ q.1 = 0 := by
    rw [hd.fderiv] at hκzero
    exact hκzero
  have ht : v.1 = 0 := (mul_eq_zero.mp hclock).resolve_right hκne
  let S : E →L[ℝ] G := fderiv ℝ (fun x => f (q.1, x)) q.2
  have hin : HasFDerivAt (fun x : E => (q.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have hS : S = (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    (((hf.differentiable (by simp) q).hasFDerivAt).comp q.2 hin).fderiv
  have hs : S v.2 = 0 := by
    rw [hS]
    change fderiv ℝ f q (0, v.2) = 0
    have he : (0, v.2) = v := Prod.ext ht.symm rfl
    rwa [he]
  exact Prod.ext ht ((injective_iff_map_eq_zero S).mp hi v.2 hs)

variable {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [FiniteDimensional ℝ B] [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
  [LindelofSpace (X × (ℝ × E))]

theorem exists_small_clock_velocity_immersion {b : X → ℝ × E}
    {f : ℝ × E → G} {κ : ℝ → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ × E) ∞ b) (hf : ContDiff ℝ ∞ f) (hκ : ContDiff ℝ ∞ κ)
    (hi : ∀ z, Injective (fderiv ℝ (fun x => f ((b z).1, x)) (b z).2))
    (hκne : ∀ z, deriv κ (b z).1 ≠ 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ (ℝ × E) < Module.finrank ℝ G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : G, ‖a‖ < ε ∧ ContDiff ℝ ∞ (perturb f κ a) ∧
      (∀ z, Injective (fderiv ℝ (perturb f κ a) (b z))) ∧
      FamilyDoublePoints.doublePoints (perturb f κ a) = FamilyDoublePoints.doublePoints f := by
  obtain ⟨a, ha, hsmooth, hkernel⟩ :=
    WeightedPerturbation.exists_small_parameter_with_common_kernel hb hf
      (hκ.comp contDiff_fst) hdim hε
  refine ⟨a, ha, hsmooth, ?_, doublePoints_perturb f κ a⟩
  intro z
  apply (injective_iff_map_eq_zero (fderiv ℝ (perturb f κ a) (b z))).mpr
  intro v hv
  obtain ⟨hfzero, hκzero⟩ := (hkernel z v).mp hv
  exact common_kernel_zero hf hκ (b z) (hi z) (hκne z) v hfzero hκzero

end Wikipedia.HopfProblem.OrbitPair.ClockVelocity

namespace Wikipedia.HopfProblem.OrbitPair.ClockVelocity

open Wikipedia.SmoothSixDPoincare

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]

theorem exists_small_linear_clock_parameter (D : ℝ × E →L[ℝ] G)
    (hi : Injective (D.comp (ContinuousLinearMap.inr ℝ ℝ E)))
    (hdim : 1 + Module.finrank ℝ (ℝ × E) < Module.finrank ℝ G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : G, ‖a‖ < ε ∧ Injective (D + (ContinuousLinearMap.fst ℝ ℝ E).smulRight a) := by
  have hin : HasFDerivAt (fun x : E => (0, x)) (ContinuousLinearMap.inr ℝ ℝ E) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : E)).prodMk (hasFDerivAt_id (0 : E))
  have hsp : Injective (fderiv ℝ (fun x : E => D (0, x)) 0) := by
    have he : fderiv ℝ (fun x : E => D (0, x)) 0 =
        D.comp (ContinuousLinearMap.inr ℝ ℝ E) := (D.hasFDerivAt.comp 0 hin).fderiv
    rw [he]
    exact hi
  obtain ⟨a, ha, -, hfull, -⟩ := exists_small_clock_velocity_immersion
    (I := 𝓘(ℝ, ℝ))
    (b := fun _ : ℝ => (0 : ℝ × E)) (f := D) (κ := id)
    contMDiff_const D.contDiff contDiff_id (fun _ => hsp)
    (fun _ => by simp) (by simpa only [Module.finrank_self] using hdim) hε
  have hd : HasFDerivAt (perturb D id a)
      (D + (ContinuousLinearMap.fst ℝ ℝ E).smulRight a) (0 : ℝ × E) :=
    D.hasFDerivAt.add (hasFDerivAt_fst.smul_const a)
  refine ⟨a, ha, ?_⟩
  have hh := hfull 0
  rwa [hd.fderiv] at hh

end Wikipedia.HopfProblem.OrbitPair.ClockVelocity
