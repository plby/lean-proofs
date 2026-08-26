import ErdosProblems.Erdos796.MeisselMertensProof

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A square-root prime-harmonic estimate

This small module records the consequence of the clean Meissel--Mertens
limit needed when summing the uniform prime-number-theorem error over primes
up to `sqrt n`.
-/

namespace Erdos796

open Filter Topology Asymptotics

/-- The Meissel--Mertens limit pulled back along the natural square root. -/
theorem primeHarmonic_sqrt_sub_loglog_tendsto :
    Tendsto
      (fun n : ℕ =>
        primeHarmonic n.sqrt -
          Real.log (Real.log (n.sqrt : ℝ)))
      atTop (nhds Mertens.M) := by
  exact meisselMertensConstant.comp tendsto_natSqrt_atTop

/-- The prime harmonic sum below `sqrt n` grows more slowly than
`log (sqrt n)`. -/
theorem primeHarmonic_sqrt_div_log_sqrt_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        primeHarmonic n.sqrt / Real.log (n.sqrt : ℝ))
      atTop (nhds 0) := by
  have hden : Tendsto
      (fun n : ℕ => Real.log (n.sqrt : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natSqrtCast_atTop
  have herr : Tendsto
      (fun n : ℕ =>
        (primeHarmonic n.sqrt -
            Real.log (Real.log (n.sqrt : ℝ))) /
          Real.log (n.sqrt : ℝ))
      atTop (nhds 0) :=
    primeHarmonic_sqrt_sub_loglog_tendsto.div_atTop hden
  have hlog : Tendsto
      (fun n : ℕ =>
        Real.log (Real.log (n.sqrt : ℝ)) /
          Real.log (n.sqrt : ℝ))
      atTop (nhds 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hden
  have hsum := herr.add hlog
  simpa only [zero_add] using! hsum.congr'
    (Eventually.of_forall fun n => by ring)

end Erdos796
