import Wikipedia.HopfProblem.OrbitPairCenteredCoordinateDerivative
import Wikipedia.HopfProblem.OrbitPairSupportedAmbientClock
import Wikipedia.HopfProblem.OrbitPairClockVelocityImmersion

/-!
# Exact native derivative of an ambient clock at its fixed time

At the center of an actual target chart, a cutoff with value one and a
clock with value zero and derivative one add exactly one arbitrary time
velocity to the full native derivative. The spatial derivative and the
entire chosen time slice are unchanged.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.ClockVelocity

open Wikipedia.SmoothSixDPoincare

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

def nativeDerivative (F : ℝ × M → N) (q : ℝ × M) : ℝ × E →L[ℝ] G :=
  mfderiv (𝓘(ℝ, ℝ).prod I) J F q

def centeredClockFamily (F : ℝ × M → N) (q : ℝ × M)
    (β : G → ℝ) (κ : ℝ → ℝ) (a : G) : ℝ × M → N :=
  NativeFamily.ambientFamily F
    (clockAmbient (NativeCenteredChart.chart (I := J) (F q)) β κ a)

theorem centeredClockFamily_fixed_time (F : ℝ × M → N) (q : ℝ × M)
    (β : G → ℝ) {κ : ℝ → ℝ} (a : G) (hκzero : κ q.1 = 0) (x : M) :
    centeredClockFamily (J := J) F q β κ a (q.1, x) = F (q.1, x) := by
  change SupportedDiffeomorph.bumpFamily _ β (κ q.1 • a, F (q.1, x)) = F (q.1, x)
  rw [hκzero, zero_smul]
  exact SupportedDiffeomorph.bumpFamily_zero _ β _

theorem nativeDerivative_centeredClockFamily {F : ℝ × M → N} (q : ℝ × M)
    {β : G → ℝ} {κ : ℝ → ℝ} (a : G)
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hnew : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (centeredClockFamily (J := J) F q β κ a))
    (hβ : ContDiff ℝ ∞ β) (hβone : β 0 = 1)
    (hκ : ContDiff ℝ ∞ κ) (hκzero : κ q.1 = 0) (hκderiv : deriv κ q.1 = 1) :
    nativeDerivative (I := I) (J := J) (centeredClockFamily (J := J) F q β κ a) q =
      nativeDerivative (I := I) (J := J) F q +
        (ContinuousLinearMap.fst ℝ ℝ E).smulRight a := by
  let c := NativeCenteredChart.chart (I := 𝓘(ℝ, ℝ).prod I) q
  let Φ := NativeCenteredChart.chart (I := J) (F q)
  let f : ℝ × E → G := NativeCenteredChart.coordinates (I := 𝓘(ℝ, ℝ).prod I) (J := J) F q
  let D : ℝ × E →L[ℝ] G := nativeDerivative (I := I) (J := J) F q
  let T : ℝ × E →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E
  let g : ℝ × E → G := fun u => f u + (β (f u) * κ (u.1 + q.1)) • a
  let F' := centeredClockFamily (J := J) F q β κ a
  have hf0 : f 0 = 0 := NativeCenteredChart.coordinates_zero F q
  have hf : ContDiffAt ℝ ∞ f 0 := NativeCenteredChart.coordinates_contDiffAt q hF.contMDiffAt
  have hfd : HasFDerivAt f D 0 := by
    have hd := (hf.differentiableAt (by simp)).hasFDerivAt
    have he : fderiv ℝ f 0 = D := NativeCenteredChart.fderiv_coordinates q hF.contMDiffAt
    rwa [he] at hd
  have hκd : HasDerivAt κ 1 q.1 := by
    have hd := (hκ.differentiable (by simp) q.1).hasDerivAt
    rwa [hκderiv] at hd
  have ht : HasFDerivAt (fun u : ℝ × E => u.1 + q.1) T 0 :=
    hasFDerivAt_fst.add_const q.1
  have hκt : HasFDerivAt (fun u : ℝ × E => κ (u.1 + q.1)) T 0 := by
    have hd := hκd.comp_hasFDerivAt_of_eq 0 ht (by simp)
    convert! hd using 1 <;> simp only [one_smul]
  have hβf := ((hβ.differentiable (by simp) (f 0)).hasFDerivAt).comp 0 hfd
  have hw : HasFDerivAt (fun u : ℝ × E => β (f u) * κ (u.1 + q.1)) T 0 := by
    have hd := hβf.mul hκt
    convert! hd using 1 <;>
      simp only [comp_apply, hf0, hβone, Prod.fst_zero, zero_add, hκzero,
        one_smul, zero_smul, add_zero]
  have hg : HasFDerivAt g (D + T.smulRight a) 0 := hfd.add (hw.smul_const a)
  have hg0 : g 0 = 0 := by simp only [g, hf0, Prod.fst_zero, zero_add, hκzero,
    mul_zero, zero_smul, add_zero]
  have hfixed : F' q = F q := centeredClockFamily_fixed_time F q β a hκzero q.2
  have heold : F ∘ c =ᶠ[𝓝 0] Φ ∘ f := NativeCenteredChart.coordinates_germ q hF.continuous.continuousAt
  have hfs : ∀ᶠ u in 𝓝 (0 : ℝ × E), f u ∈ Φ.source := by
    have hn : Φ.source ∈ 𝓝 (f 0) := by
      rw [hf0]
      exact Φ.open_source.mem_nhds (NativeCenteredChart.zero_mem_source (F q))
    exact hf.continuousAt.preimage_mem_nhds hn
  have he : F' ∘ c =ᶠ[𝓝 0] Φ ∘ g := by
    filter_upwards [heold, hfs] with u hu hfu
    change F (c u) = Φ (f u) at hu
    change SupportedDiffeomorph.bumpFamily Φ β (κ (c u).1 • a, F (c u)) = Φ (g u)
    rw [hu, NativeCenteredChart.chart_prod_fst]
    rw [SupportedDiffeomorph.bumpFamily_chart Φ β _ hfu]
    change Φ (f u + β (f u) • (κ (u.1 + q.1) • a)) = Φ (g u)
    simp only [g, mul_smul]
  have hcoord : fderiv ℝ g 0 = nativeDerivative (I := I) (J := J) F' q := by
    apply NativeCenteredChart.coordinate_germ_derivative
      (hnew.mdifferentiableAt (by simp)) hg.differentiableAt hg0
    change F' ∘ c =ᶠ[𝓝 0] NativeCenteredChart.chart (I := J) (F' q) ∘ g
    rw [hfixed]
    exact he
  exact hcoord.symm.trans hg.fderiv

end Wikipedia.HopfProblem.OrbitPair.ClockVelocity
