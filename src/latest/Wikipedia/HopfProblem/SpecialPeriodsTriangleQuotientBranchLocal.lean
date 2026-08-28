import Wikipedia.HopfProblem.SpecialPeriodsTriangleBranchCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientCayleyBalls
import Wikipedia.HopfProblem.EllipticDiscLocalInverse

/-!
# Local analytic inverses of the normalized elliptic branch coordinate

The normalized centered Cayley coordinate is locally biholomorphic on the
whole upper half-plane.  Its positive integral powers remain locally
biholomorphic away from the center.  These are the actual inverse branches
used to prove compatibility of the full triangle quotient charts.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

section EventualCongruence

variable {E F H K M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N]
    {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ F K} {n : ℕ∞ω}

/-- Local biholomorphism is unchanged by altering a function outside a
neighbourhood of the point.  Restrict the actual inverse chart to that
neighbourhood; no inverse is supplied as an extra hypothesis. -/
theorem isLocalDiffeomorphAt_congr_of_eventuallyEq {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hgf : g =ᶠ[𝓝 x] f) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨U, hUf, hU, hxU⟩ := mem_nhds_iff.mp hgf
  obtain ⟨Φ, hx, hΦ⟩ := hf
  let Ψ : PartialDiffeomorph I J M N n :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨Ψ, ⟨hx, hxU⟩, ?_⟩
  intro y hy
  exact (hUf hy.2).trans (hΦ hy.1)

end EventualCongruence

namespace SpecialPeriods.Triangle

/-- Nonzero complex scaling as an actual biholomorphism. -/
def complexDivideBiholomorph (c : ℂ) (hc : c ≠ 0) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω where
  toFun z := z / c
  invFun z := z * c
  left_inv z := div_mul_cancel₀ z hc
  right_inv z := mul_div_cancel_right₀ z hc
  contMDiff_toFun := contMDiff_id.div₀ contMDiff_const (fun _ => hc)
  contMDiff_invFun := contMDiff_id.mul contMDiff_const

/-- The global normalized Cayley coordinate underlying each chosen local ball. -/
def normalizedCayley (a : ℍ) (r : ℝ) (z : ℍ) : ℂ := cayleyCoordinate a z / (r : ℂ)

theorem normalizedCayley_holomorphic (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayley a r) :=
  (cayleyCoordinate_holomorphic a).div₀ contMDiff_const
    (fun _ => Complex.ofReal_ne_zero.mpr hr)

/-- Normalization by a nonzero radius does not create a critical point. -/
theorem normalizedCayley_isLocalDiffeomorph (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayley a r) := by
  intro z
  have hc := ((cayleyBiholomorph a).isLocalDiffeomorph z).comp
    (K := 𝓘(ℂ)) (P := ℂ) (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) unitDisc (toDisc a z))
  exact hc.comp (K := 𝓘(ℂ)) (P := ℂ)
    ((complexDivideBiholomorph (r : ℂ) (Complex.ofReal_ne_zero.mpr hr)).isLocalDiffeomorph
      (cayleyCoordinate a z))

/-- The global complex expression for the local ramified quotient chart. -/
def normalizedCayleyBranch (a : ℍ) (r : ℝ) (m : ℕ) (z : ℍ) : ℂ :=
  normalizedCayley a r z ^ m

theorem normalizedCayleyBranch_holomorphic (a : ℍ) (r : ℝ) (hr : r ≠ 0) (m : ℕ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayleyBranch a r m) :=
  (normalizedCayley_holomorphic a r hr).pow m

theorem normalizedCayleyBranch_eq_zero_iff (a z : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    normalizedCayleyBranch a r m z = 0 ↔ z = a := by
  simp only [normalizedCayleyBranch, normalizedCayley, pow_eq_zero_iff hm.ne',
    div_eq_zero_iff, Complex.ofReal_eq_zero, hr, or_false, cayleyCoordinate_eq_zero_iff]

/-- The actual positive-power coordinate is locally biholomorphic away
from its one ramification point. -/
theorem normalizedCayleyBranch_isLocalDiffeomorphAt (a z : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) (hm : 0 < m) (hz : z ≠ a) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayleyBranch a r m) z := by
  have hc : normalizedCayley a r z ≠ 0 :=
    div_ne_zero ((cayleyCoordinate_eq_zero_iff a z).not.mpr hz)
      (Complex.ofReal_ne_zero.mpr hr)
  exact (normalizedCayley_isLocalDiffeomorph a r hr z).comp (K := 𝓘(ℂ)) (P := ℂ)
    (Elliptic.complexPower_isLocalDiffeomorphAt m hm (normalizedCayley a r z) hc)

end SpecialPeriods.Triangle

end Wikipedia.HopfProblem
