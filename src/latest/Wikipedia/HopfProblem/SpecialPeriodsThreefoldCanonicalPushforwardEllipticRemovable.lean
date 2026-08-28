import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovableFilters
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovableGrowth

/-!
# Removability from a less singular ramified pullback

Suppose a finite analytic branch `g` has order `n` over `b`, while the
actual pulled-back coefficient `s ^ k * F (g s)` extends continuously
over zero with `k < n`.  The product `(q - b) * F q` tends to zero:
upstairs it is `s ^ (n - k) * u s * A s` for an analytic unit `u`.
The exact punctured-neighborhood image of `g` then gives the downstairs
limit.  Punctured analyticity of `F` makes its singularity removable,
with the extension value equal to its actual punctured limit.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.CanonicalPushforwardEllipticRemovable

open TriangleHolomorphicDifferentialsRemovable

/-- A continuously extended ramified pullback whose compensating power
is smaller than the ramification order forces the local-parameter
product downstairs to tend to zero. -/
theorem sub_mul_tendsto_zero_of_ramified_pullback
    {F g A : ℂ → ℂ} {b : ℂ} {n k : ℕ}
    (hg : AnalyticAt ℂ g 0) (hgb : g 0 = b)
    (horder : analyticOrderAt (fun s => g s - b) 0 = (n : ℕ∞))
    (hk : k < n) (hA : ContinuousAt A 0)
    (hcomp : A =ᶠ[𝓝[≠] 0] (fun s => s ^ k * F (g s))) :
    Tendsto (fun q => (q - b) * F q) (𝓝[≠] b) (𝓝 0) := by
  have hfinite : analyticOrderAt (fun s => g s - g 0) 0 ≠ ⊤ := by
    rw [hgb, horder]
    exact ENat.natCast_ne_top n
  have hmap := map_nhdsNE_eq_of_finite_order hg hfinite
  rw [hgb] at hmap
  rw [← hmap, tendsto_map'_iff]
  obtain ⟨u, hu, _, hfactor⟩ :=
    (hg.sub analyticAt_const).analyticOrderAt_eq_natCast.mp horder
  have hk0 : n - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hk)
  have hlim : Tendsto (fun s : ℂ => s ^ (n - k) * u s * A s)
      (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℂ => s ^ (n - k) * u s * A s) 0 :=
      ((continuousAt_id.pow (n - k)).mul hu.continuousAt).mul hA
    simpa only [zero_pow hk0, zero_mul] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [hcomp, hfactor.filter_mono nhdsWithin_le_nhds] with s hs hgs
  change s ^ (n - k) * u s * A s = (g s - b) * F (g s)
  have he : g s - b = s ^ n * u s := by
    simpa only [Pi.sub_apply, sub_zero, smul_eq_mul] using hgs
  rw [hs, he]
  calc
    s ^ (n - k) * u s * (s ^ k * F (g s)) =
        s ^ (n - k + k) * u s * F (g s) := by
      rw [pow_add]
      ring
    _ = s ^ n * u s * F (g s) := by
      rw [Nat.sub_add_cancel (Nat.le_of_lt hk)]

/-- The downstairs function has a finite punctured limit when it is
analytic away from the ramification value. -/
theorem tendsto_limUnder_of_ramified_pullback
    {F g A : ℂ → ℂ} {b : ℂ} {n k : ℕ}
    (hg : AnalyticAt ℂ g 0) (hgb : g 0 = b)
    (horder : analyticOrderAt (fun s => g s - b) 0 = (n : ℕ∞))
    (hk : k < n) (hA : ContinuousAt A 0)
    (hcomp : A =ᶠ[𝓝[≠] 0] (fun s => s ^ k * F (g s)))
    (hF : ∀ᶠ q in 𝓝[≠] b, AnalyticAt ℂ F q) :
    Tendsto F (𝓝[≠] b) (𝓝 (limUnder (𝓝[≠] b) F)) :=
  tendsto_limUnder_of_sub_mul_tendsto_zero hF
    (sub_mul_tendsto_zero_of_ramified_pullback hg hgb horder hk hA hcomp)

/-- Updating at the actual punctured limit removes the singularity. -/
theorem analyticAt_update_limUnder_of_ramified_pullback
    {F g A : ℂ → ℂ} {b : ℂ} {n k : ℕ}
    (hg : AnalyticAt ℂ g 0) (hgb : g 0 = b)
    (horder : analyticOrderAt (fun s => g s - b) 0 = (n : ℕ∞))
    (hk : k < n) (hA : ContinuousAt A 0)
    (hcomp : A =ᶠ[𝓝[≠] 0] (fun s => s ^ k * F (g s)))
    (hF : ∀ᶠ q in 𝓝[≠] b, AnalyticAt ℂ F q) :
    AnalyticAt ℂ (Function.update F b (limUnder (𝓝[≠] b) F)) b :=
  analyticAt_update_limUnder_of_sub_mul_tendsto_zero hF
    (sub_mul_tendsto_zero_of_ramified_pullback hg hgb horder hk hA hcomp)

/-- An actual analytic extension agrees with `F` on a punctured
neighborhood and takes its punctured-limit value at the center. -/
theorem exists_analytic_extension_of_ramified_pullback
    {F g A : ℂ → ℂ} {b : ℂ} {n k : ℕ}
    (hg : AnalyticAt ℂ g 0) (hgb : g 0 = b)
    (horder : analyticOrderAt (fun s => g s - b) 0 = (n : ℕ∞))
    (hk : k < n) (hA : ContinuousAt A 0)
    (hcomp : A =ᶠ[𝓝[≠] 0] (fun s => s ^ k * F (g s)))
    (hF : ∀ᶠ q in 𝓝[≠] b, AnalyticAt ℂ F q) :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext b ∧
      Fext =ᶠ[𝓝[≠] b] F ∧ Fext b = limUnder (𝓝[≠] b) F :=
  exists_analytic_extension_of_sub_mul_tendsto_zero hF
    (sub_mul_tendsto_zero_of_ramified_pullback hg hgb horder hk hA hcomp)

end Wikipedia.HopfProblem.CanonicalPushforwardEllipticRemovable
