import Wikipedia.HopfProblem.CuspPuncturedBasic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The logarithmic domain is a contractible half-space

The inverse image of a punctured disc under the normalized exponential is
an upper half-plane. Allowing both fibre logarithms to vary therefore gives
a convex, nonempty, and simply connected logarithmic covering domain.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspUniformization

theorem mem_logDomain_iff_im (ε : ℝ) (hε : 0 < ε) (p : ℂ × ComplexPlane₂) :
    p ∈ logDomain ε ↔ -Real.log ε / (2 * Real.pi) < p.1.im := by
  rw [mem_logDomain,
    ← Real.log_lt_log_iff (norm_pos_iff.mpr (exponential_ne_zero p.1)) hε,
    log_norm_exponential, div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
  constructor <;> intro h <;> nlinarith

theorem logDomain_eq_halfSpace (ε : ℝ) (hε : 0 < ε) :
    (logDomain ε : Set (ℂ × ComplexPlane₂)) =
      {p | -Real.log ε / (2 * Real.pi) < p.1.im} := by
  ext p
  exact mem_logDomain_iff_im ε hε p

theorem logDomain_convex (ε : ℝ) (hε : 0 < ε) :
    Convex ℝ (logDomain ε : Set (ℂ × ComplexPlane₂)) := by
  rw [logDomain_eq_halfSpace ε hε]
  exact (convex_Ioi (-Real.log ε / (2 * Real.pi))).linear_preimage
    (Complex.imLm.comp (LinearMap.fst ℝ ℂ ComplexPlane₂))

theorem logDomain_nonempty (ε : ℝ) (hε : 0 < ε) :
    (logDomain ε : Set (ℂ × ComplexPlane₂)).Nonempty := by
  refine ⟨(((↑(-Real.log ε / (2 * Real.pi) + 1) : ℂ) * Complex.I), 0), ?_⟩
  apply (mem_logDomain_iff_im ε hε _).mpr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  linarith

theorem logDomain_isPathConnected (ε : ℝ) (hε : 0 < ε) :
    IsPathConnected (logDomain ε : Set (ℂ × ComplexPlane₂)) :=
  (logDomain_convex ε hε).isPathConnected (logDomain_nonempty ε hε)

theorem logCover_contractibleSpace (ε : ℝ) (hε : 0 < ε) :
    ContractibleSpace (LogCover ε) :=
  (logDomain_convex ε hε).contractibleSpace (logDomain_nonempty ε hε)

theorem logCover_simplyConnectedSpace (ε : ℝ) (hε : 0 < ε) :
    SimplyConnectedSpace (LogCover ε) := by
  let := logCover_contractibleSpace ε hε
  infer_instance

end Wikipedia.HopfProblem.CuspUniformization
