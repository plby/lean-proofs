import ErdosProblems.Erdos4.FiberExclusions

/-!
# Uniform lower bounds for the actual arithmetic fibers

The modulus is fixed. The completion endpoint and the frozen cofactor
may vary throughout the divisor cutoff. A bounded logarithmic floor
error is absorbed uniformly, and the exclusion loss is controlled by
the coefficient label's reciprocal prime mass.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.FiberAsymptotic

open PrimitiveProfile WeightedHarmonic FiberExclusions ArithmeticFibers
open DivisorCoefficients CutoffSimplex

theorem primitive_lipschitz {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |primitive m k s - primitive m k t| ≤ |s - t| := by
  have hmpos : 0 < m := by linarith
  have hder : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (primitive m k) (profile m k x) (Set.Ici 0) x := by
    intro x hx
    exact (hasDerivAt_primitive hmpos hk hx).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ici (0 : ℝ), ‖profile m k x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (profile_pos hmpos.le hk hx)]
    exact profile_le_one hm hk hx
  simpa only [Real.norm_eq_abs, one_mul] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Ici 0) ht hs

theorem density_pos {W : ℕ} (hW : 0 < W) :
    0 < BoundedGaps.Maynard.coprimeHarmonicDensity W := by
  unfold BoundedGaps.Maynard.coprimeHarmonicDensity
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hW) (by exact_mod_cast hW)

theorem uniform_quotient {W : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧ ∀ r : ℕ, 1 ≤ r → r ≤ R →
      |weightedSum W m k R (R / r) -
        BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log R *
          primitive m k ((Real.log R - Real.log r) / Real.log R)| ≤ ε * Real.log R := by
  let ρ := BoundedGaps.Maynard.coprimeHarmonicDensity W
  have hρ : 0 ≤ ρ := (density_pos hW).le
  have hhalf : 0 < ε / 2 := by linarith
  have hloglim : Tendsto (fun R : ℕ => Real.log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ R : ℕ in atTop, ρ * Real.log 2 / (ε / 2) ≤ Real.log R :=
    hloglim.eventually (eventually_ge_atTop _)
  filter_upwards [uniform_asymptotic hW hSq hm hk hhalf, hlarge] with R hR hlarge
  refine ⟨hR.1, ?_⟩
  intro r hr hrR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR.1)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hx : (1 : ℝ) ≤ (R : ℝ) / r := (one_le_div hrpos).mpr (by exact_mod_cast hrR)
  have hT : 1 ≤ R / r := Nat.div_pos hrR (by omega)
  have hfirst := hR.2 (R / r) hT (Nat.div_le_self _ _)
  have hfloor := HarmonicUniform.log_floor_error_le hx
  rw [Nat.floor_div_eq_div, Real.log_div hRpos.ne' hrpos.ne'] at hfloor
  have hparam : 0 ≤ (Real.log R - Real.log r) / Real.log R :=
    div_nonneg (sub_nonneg.mpr (Real.log_le_log hrpos (by exact_mod_cast hrR))) hlog.le
  have hprim := primitive_lipschitz hm hk
    (div_nonneg (Real.log_natCast_nonneg (R / r)) hlog.le) hparam
  have hnorm : |Real.log (R / r : ℕ) / Real.log R -
      (Real.log R - Real.log r) / Real.log R| ≤ Real.log 2 / Real.log R := by
    rw [← sub_div, abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right hfloor hlog.le
  have hsecond : |ρ * Real.log R *
      (primitive m k (Real.log (R / r : ℕ) / Real.log R) -
        primitive m k ((Real.log R - Real.log r) / Real.log R))| ≤ ρ * Real.log 2 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hρ hlog.le)]
    calc
      _ ≤ ρ * Real.log R * (Real.log 2 / Real.log R) :=
        mul_le_mul_of_nonneg_left (hprim.trans hnorm) (mul_nonneg hρ hlog.le)
      _ = ρ * Real.log 2 := by field_simp
  have hsmall : ρ * Real.log 2 ≤ (ε / 2) * Real.log R := by
    have hh := (div_le_iff₀ hhalf).mp hlarge
    nlinarith
  have hsplit : weightedSum W m k R (R / r) -
      ρ * Real.log R * primitive m k ((Real.log R - Real.log r) / Real.log R) =
      (weightedSum W m k R (R / r) -
        ρ * Real.log R * primitive m k (Real.log (R / r : ℕ) / Real.log R)) +
      ρ * Real.log R * (primitive m k (Real.log (R / r : ℕ) / Real.log R) -
        primitive m k ((Real.log R - Real.log r) / Real.log R)) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hfirst (hsecond.trans hsmall)).trans_eq (by ring))

theorem eventually_mean_le {W : ℕ} (hW : 0 < W) (hSq : Squarefree W) :
    ∀ᶠ R : ℕ in atTop,
      BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W R ≤
        2 * BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log R := by
  filter_upwards [HarmonicUniform.fixed_modulus_uniform hW hSq (density_pos hW)] with R hR
  have hh := (abs_le.mp (hR.2 R le_rfl)).2
  linarith

/-- On every supported label of reciprocal mass at most `η`, the
arithmetic fiber has the variational lower bound with error `δ + 2η`.
The assertion is uniform in the anchor and in all supported labels. -/
theorem eventually_fiber_lower {m : ℝ} (hm : 1 ≤ m) (k K : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) :
    ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧
      ∀ (j : Fin k) (a : primeWindow K R → Option (Fin k)),
      totalDivisor (fun p : primeWindow K R => (p : ℕ)) a ≤ R →
      CoefficientMass.reciprocalMass (fun p : primeWindow K R => (p : ℕ)) a ≤ η →
      BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Real.log R *
        (primitive m k (1 - (∑ i : Fin k,
          coordinate R (fun p : primeWindow K R => (p : ℕ)) a i) +
          coordinate R (fun p : primeWindow K R => (p : ℕ)) a j) - δ - 2 * η) ≤
      IdealAction.fiberSum m R (fun p : primeWindow K R => (p : ℕ)) j a := by
  let ρ := BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K)
  have hρ : 0 < ρ := density_pos (primorial_pos K)
  have hε : 0 < ρ * δ := mul_pos hρ hδ
  filter_upwards [uniform_quotient (primorial_pos K) (squarefree_primorial K) hm
      (Nat.cast_nonneg k) hε,
    eventually_mean_le (primorial_pos K) (squarefree_primorial K)] with R hR hmean
  refine ⟨hR.1, ?_⟩
  intro j a ha hmass
  let ell : primeWindow K R → ℕ := fun p => p
  have hell : ∀ p, 1 ≤ ell p := fun p => (mem_primeWindow.mp p.property).1.one_le
  have hr : 1 ≤ cofactor ell j a := cofactor_pos ell hell j a
  have hrR : cofactor ell j a ≤ R := (cofactor_le_totalDivisor ell hell j a).trans ha
  have happrox := (abs_le.mp (hR.2 (cofactor ell j a) hr hrR)).1
  have hexclude := primeWindow_weightedSum_sub_mass_le hm hR.1 K j a
  have hcost : BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean (primorial K) R *
      CoefficientMass.reciprocalMass ell a ≤ 2 * ρ * Real.log R * η := by
    calc
      _ ≤ BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean (primorial K) R * η :=
        mul_le_mul_of_nonneg_left hmass (mean_nonneg (primorial K) R)
      _ ≤ _ := mul_le_mul_of_nonneg_right hmean hη
  rw [completion_parameter_eq hR.1 ell hell j a]
  change ρ * Real.log R * _ ≤ IdealAction.fiberSum m R ell j a
  nlinarith

end Erdos4.FiberAsymptotic
