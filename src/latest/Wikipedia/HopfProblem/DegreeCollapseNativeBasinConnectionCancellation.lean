import Wikipedia.HopfProblem.DegreeCollapseTransverseBasinCancellation
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowTimeDiffeomorph

/-!
# Native cancellation directly from an original transverse basin connection

Construct the entire local cancellation data from the original connection.
Its retained orbit equivalences and reference-point time shift transport
the given native transverse basin sheets into the actual cancellation
basins. No endpoint, cylinder, phase or cancellation data are supplied.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ}
  {A B HA HB X Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace HA] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]

open Classical in
theorem cancel_unique_connection_of_transverse_basin_sheets {f : M → ℝ} {p q z : M}
    (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hdim : Module.finrank ℝ E = m + 1)
    (hindex : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hinj : InjOn f (criticalPoints E f))
    (hpc : p ∈ criticalPoints E f) (hqc : q ∈ criticalPoints E f) (hpq : f p < f q)
    {c d : ℝ} (hc : c < f p) (hd : f q < d)
    (hpair : ∀ x ∈ criticalPoints E f, f x ∈ Icc c d → x = p ∨ x = q)
    (hp : Tendsto (fun t => F t z) atTop (𝓝 p))
    (hq : Tendsto (fun t => F t z) atBot (𝓝 q))
    (hunique : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 q) →
      Tendsto (fun t => F t x) atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x)
    (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x)
    {S : X → M} {T : Y → M} {x : X} {y : Y}
    (hS : MDifferentiableAt I 𝓘(ℝ, E) S x) (hT : MDifferentiableAt I' 𝓘(ℝ, E) T y)
    (hS0 : S x = z) (hT0 : T y = z)
    (hSbasin : ∀ᶠ u in 𝓝 x, Tendsto (fun t => F t (S u)) atBot (𝓝 q))
    (hTbasin : ∀ᶠ u in 𝓝 y, Tendsto (fun t => F t (T u)) atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) S T x y) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔ x ∈ criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
      ∀ x, f x ∉ Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨D, -, hgeometry, t₀, ht₀⟩ := exists_native_connection_cancellation_data cp cq
    hf hdim hindex V hV hzero hdesc F hF hpc hqc hpq hc hd hpair hp hq hunique heqp heqq
  let τ := SmoothODE.nativeFlowTimeDiffeomorph_of_field hV F hF t₀
  have hτ (u : M) : τ u = F t₀ u := rfl
  have hS' : MDifferentiableAt I 𝓘(ℝ, E) (τ ∘ S) x :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp x hS
  have hT' : MDifferentiableAt I' 𝓘(ℝ, E) (τ ∘ T) y :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp y hT
  have hS0' : (τ ∘ S) x = D.A 0 := by rw [comp_apply, hτ, hS0, ht₀]
  have hT0' : (τ ∘ T) y = D.A 0 := by rw [comp_apply, hτ, hT0, ht₀]
  have hSb : ∀ᶠ u in 𝓝 x, Tendsto (fun t => D.flow t ((τ ∘ S) u)) atBot (𝓝 q) := by
    filter_upwards [hSbasin] with u hu
    apply ((hgeometry ((τ ∘ S) u)).2.2 q).mpr
    exact (flow_time_atBot_limit_iff F t₀ (S u) q).mpr hu
  have hTb : ∀ᶠ u in 𝓝 y, Tendsto (fun t => D.flow t ((τ ∘ T) u)) atTop (𝓝 p) := by
    filter_upwards [hTbasin] with u hu
    apply ((hgeometry ((τ ∘ T) u)).2.1 p).mpr
    exact (flow_time_atTop_limit_iff F t₀ (T u) p).mpr hu
  have ht : NativeTransversality.At I I' 𝓘(ℝ, E) (τ ∘ S) (τ ∘ T) x y :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff
      τ.toPartialDiffeomorph hS hT (hT0.trans hS0.symm) (mem_univ _)).mp htrans
  exact D.cancel_of_transverse_basin_sheets hS' hT' hS0' hT0' hSb hTb ht
    hf hm hinj hpc hqc hpq hc hd hpair

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
