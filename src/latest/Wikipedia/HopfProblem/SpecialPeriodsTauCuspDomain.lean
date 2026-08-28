import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyBase
import Wikipedia.HopfProblem.CuspPuncturedDomain
import Mathlib.Analysis.Complex.Periodic

/-!
# The connected logarithmic cusp domain

The actual logarithmic preimage of a positive-radius disc is an open upper
half-plane. Its convexity gives the connectedness needed for a single
integer sheet choice. The normalized exponential is also the width-one
parameter used in modular q-expansions.
-/

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

theorem mem_logBase_iff_im (r : ℝ) (hr : 0 < r) (s : ℂ) :
    s ∈ CuspFamily.logBase r ↔ -Real.log r / (2 * Real.pi) < s.im :=
  mem_logDomain_iff_im r hr (s, 0)

theorem logBase_eq_halfSpace (r : ℝ) (hr : 0 < r) :
    (CuspFamily.logBase r : Set ℂ) =
      {s | -Real.log r / (2 * Real.pi) < s.im} := by
  ext s
  exact mem_logBase_iff_im r hr s

theorem logBase_convex (r : ℝ) (hr : 0 < r) :
    Convex ℝ (CuspFamily.logBase r : Set ℂ) := by
  rw [logBase_eq_halfSpace r hr]
  exact (convex_Ioi (-Real.log r / (2 * Real.pi))).linear_preimage Complex.imLm

theorem logBase_set_nonempty (r : ℝ) (hr : 0 < r) :
    (CuspFamily.logBase r : Set ℂ).Nonempty := by
  obtain ⟨p, hp⟩ := logDomain_nonempty r hr
  exact ⟨p.1, hp⟩

theorem logBase_nonempty (r : ℝ) (hr : 0 < r) : Nonempty (CuspFamily.LogBase r) :=
  (logBase_set_nonempty r hr).to_subtype

theorem logBase_isPathConnected (r : ℝ) (hr : 0 < r) :
    IsPathConnected (CuspFamily.logBase r : Set ℂ) :=
  (logBase_convex r hr).isPathConnected (logBase_set_nonempty r hr)

theorem logBase_pathConnectedSpace (r : ℝ) (hr : 0 < r) :
    PathConnectedSpace (CuspFamily.LogBase r) :=
  isPathConnected_iff_pathConnectedSpace.mp (logBase_isPathConnected r hr)

theorem logBase_preconnectedSpace (r : ℝ) (hr : 0 < r) :
    PreconnectedSpace (CuspFamily.LogBase r) :=
  Subtype.preconnectedSpace (logBase_convex r hr).isPreconnected

theorem logBase_connectedSpace (r : ℝ) (hr : 0 < r) :
    ConnectedSpace (CuspFamily.LogBase r) :=
  Subtype.connectedSpace (logBase_isPathConnected r hr).isConnected

theorem exponential_eq_qParam_one (s : ℂ) :
    exponential s = Function.Periodic.qParam 1 s := by
  simp only [exponential, Function.Periodic.qParam, Complex.ofReal_one, div_one]

theorem qParam_eq_exponential_div (w : ℝ) (s : ℂ) :
    Function.Periodic.qParam w s = exponential (s / w) := by
  simp only [exponential, Function.Periodic.qParam, mul_div_assoc]

theorem norm_exponential_lt_one_iff (s : ℂ) :
    ‖exponential s‖ < 1 ↔ 0 < s.im := by
  simpa only [CuspFamily.mem_logBase, Real.log_one, neg_zero, zero_div] using
    mem_logBase_iff_im 1 zero_lt_one s

theorem upperHalfPlane_of_exponential_norm_lt_one {s : ℂ}
    (hs : ‖exponential s‖ < 1) : 0 < s.im :=
  (norm_exponential_lt_one_iff s).mp hs

theorem exponential_norm_lt_one_of_upperHalfPlane {s : ℂ}
    (hs : 0 < s.im) : ‖exponential s‖ < 1 :=
  (norm_exponential_lt_one_iff s).mpr hs

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
