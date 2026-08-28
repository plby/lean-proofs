import Wikipedia.HopfProblem.DegreeCollapseNativeLevelIsotopyRealization
import Wikipedia.HopfProblem.DegreeCollapseWholeLevelConnectionRealization
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelBasinSheets
import Wikipedia.HopfProblem.DegreeCollapseNativeBasinConnectionCancellation

/-!
# Exact native pair cancellation from an actual transverse level isotopy

An actual native regular-level isotopy, one basin-intersection point and
transverse level-sheet germs construct the supported field change, unique
complete connection, native basin tubes and all cancellation data. The
result removes precisely the selected critical pair from the original
Morse function. No connecting orbit or local cancellation chart is input.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

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
theorem cancel_of_transverse_level_isotopy {f : M → ℝ} {p q : M}
    (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hdim : Module.finrank ℝ E = m + 1)
    (hindex : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1)
    (V : (z : M) → TangentSpace 𝓘(ℝ, E) z)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ z ∈ criticalPoints E f, V z = 0)
    (hdesc : ∀ z, z ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0)
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hinj : InjOn f (criticalPoints E f))
    (hpc : p ∈ criticalPoints E f) (hqc : q ∈ criticalPoints E f)
    {l u a b c : ℝ} (hl : l < f p) (hu : f q < u)
    (hpair : ∀ z ∈ criticalPoints E f, f z ∈ Icc l u → z = p ∨ z = q)
    (ha : a < c) (hb : c < b) (hpc' : f p < c) (hqc' : c < f q)
    (hband : ∀ z, f z ∈ Icc a b → z ∉ criticalPoints E f)
    (hreg : ∀ z, f z = c → z ∉ criticalPoints E f)
    (heqp : ∀ᶠ z in 𝓝 p, V z = cp.descentField z)
    (heqq : ∀ᶠ z in 𝓝 q, V z = cq.descentField z) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {z : M // f z = c} {z : M // f z = c} ∞,
      IsotopicToIdentity D →
      {z : {w : M // f w = c} |
        Tendsto (fun t => F t z) atBot (𝓝 q) ∧
        Tendsto (fun t => F t (D z)) atTop (𝓝 p)}.ncard = 1 →
      ∀ (α : X → {z : M // f z = c}) (β : Y → {z : M // f z = c}) (x : X) (y : Y),
        MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
        MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
        β y = α x → NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
        (∀ᶠ z in 𝓝 x, Tendsto (fun t => F t (α z)) atBot (𝓝 q)) →
        (∀ᶠ z in 𝓝 y, Tendsto (fun t => F t (D (β z))) atTop (𝓝 p)) →
        ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
          (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
          (∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q) ∧
          ∀ z, f z ∉ Ioo l u → g =ᶠ[𝓝 z] f := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  intro D hD hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨r, C, W, V', H, G, -, -, -, -, -, -, hgeometry, hV', hG,
      hzeros, hneg, hgerms, -, hend, -, hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf hV hdesc F hF
      ha hb hband hreg (α x) D hD
  obtain ⟨hback, hforward⟩ := FlowSuspension.whole_level_basins_of_holonomy
    F H G Subtype.val D (fun z => (hgeometry z).2.1) (fun z => (hgeometry z).2.2)
    hend hleft hright
  have hαb : ∀ᶠ z in 𝓝 x, Tendsto (fun t => G t (α z)) atBot (𝓝 q) := by
    filter_upwards [hαbasin] with z hz
    exact (hback (α z) q).mpr hz
  have hβb : ∀ᶠ z in 𝓝 y, Tendsto (fun t => G t (β z)) atTop (𝓝 p) := by
    filter_upwards [hβbasin] with z hz
    exact (hforward (β z) p).mpr hz
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hαq : Tendsto (fun t => F t (α x)) atBot (𝓝 q) := hαbasin.self_of_nhds
  have hαp : Tendsto (fun t => F t (D (α x))) atTop (𝓝 p) := by
    rw [← hcross]
    exact hβbasin.self_of_nhds
  have hαeq : α x = z₀ := by
    have hh : α x ∈ {z : {w : M // f w = c} |
        Tendsto (fun t => F t z) atBot (𝓝 q) ∧
        Tendsto (fun t => F t (D z)) atTop (𝓝 p)} := ⟨hαq, hαp⟩
    rw [hz₀] at hh
    exact mem_singleton_iff.mp hh
  have huniq (z : {w : M // f w = c})
      (hzq : Tendsto (fun t => F t z) atBot (𝓝 q))
      (hzp : Tendsto (fun t => F t (D z)) atTop (𝓝 p)) : z = α x := by
    have hh : z ∈ {z : {w : M // f w = c} |
        Tendsto (fun t => F t z) atBot (𝓝 q) ∧
        Tendsto (fun t => F t (D z)) atTop (𝓝 p)} := ⟨hzq, hzp⟩
    rw [hz₀] at hh
    exact (mem_singleton_iff.mp hh).trans hαeq.symm
  obtain ⟨hqG, hpG, huniqueG⟩ := FlowSuspension.unique_connection_of_level_basin_intersection
    F G hf.continuous hqc' hpc' D (fun z => hback z q) (fun z => hforward z p)
    (α x) hαq hαp huniq
  obtain ⟨hS, hT, hS0, hT0, hSb, hTb, ht⟩ :=
    FlowSuspension.native_transverse_basin_tubes_of_level_maps hf hreg hV' G hG
      (fun z hz => hneg z (hreg z hz)) α β x y hα hβ hcross htrans hαb hβb
  have hgermp : ∀ᶠ z in 𝓝 p, V' z = cp.descentField z := by
    filter_upwards [hgerms p hpc, heqp] with z hz hz'
    exact hz.trans hz'
  have hgermq : ∀ᶠ z in 𝓝 q, V' z = cq.descentField z := by
    filter_upwards [hgerms q hqc, heqq] with z hz hz'
    exact hz.trans hz'
  exact cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex
    V' hV' (fun z hz => (hzeros z).mpr (hzero z hz)) hneg G hG hinj hpc hqc
    (hpc'.trans hqc') hl hu hpair hpG hqG huniqueG hgermp hgermq
    hS hT hS0 hT0 hSb hTb ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
