import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackWeightedTrivialization

/-!
# The canonical bundle map is genuinely locally biholomorphic

In the original bundle trivializations, inverse pullback is the weighted
product of the base local biholomorphism with the reciprocal of its actual
chart Jacobian.  The explicit weighted-product inverse therefore supplies
an actual local inverse of the canonical bundle map.
-/

noncomputable section

open Bundle Set Topology Filter
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- Restrict an actual inverse chart when two maps agree near the point. -/
private theorem localDiffeomorphAt_congr
    {f g : (Atlas.core M).TotalSpace → (Atlas.core N).TotalSpace}
    {p : (Atlas.core M).TotalSpace}
    (hf : IsLocalDiffeomorphAt Iᴷ Iᴷ ω f p) (hgf : g =ᶠ[𝓝 p] f) :
    IsLocalDiffeomorphAt Iᴷ Iᴷ ω g p := by
  obtain ⟨U, hUf, hU, hpU⟩ := mem_nhds_iff.mp hgf
  obtain ⟨Φ, hp, hΦ⟩ := hf
  let Ψ : PartialDiffeomorph Iᴷ Iᴷ (Atlas.core M).TotalSpace (Atlas.core N).TotalSpace ω :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨Ψ, ⟨hp, hpU⟩, ?_⟩
  intro q hq
  exact (hUf hq.2).trans (hΦ hq.1)

/-- Exact representation through the actual source and target bundle
trivializations on a genuine chart overlap. -/
theorem forwardMap_eq_localTriv_weighted {f : M → N}
    (hf : IsLocalDiffeomorph I I ω f) (i : atlas Model M) (j : atlas Model N)
    (p : (Atlas.core M).TotalSpace) (hi : p.proj ∈ i.val.source)
    (hj : f p.proj ∈ j.val.source) :
    forwardMap hf p = ((Atlas.core N).localTriv j).toOpenPartialHomeomorph.symm
      (weightedMap f (fun x => (chartDeterminant f i j x)⁻¹)
        ((Atlas.core M).localTriv i p)) := by
  calc
    _ = ((Atlas.core N).localTriv j).toOpenPartialHomeomorph.symm
        ((Atlas.core N).localTriv j (forwardMap hf p)) :=
      (((Atlas.core N).localTriv j).toOpenPartialHomeomorph.left_inv hj).symm
    _ = _ := congrArg ((Atlas.core N).localTriv j).toOpenPartialHomeomorph.symm
      (forwardMap_localTriv hf i j p hi hj)

/-- The map of the original canonical bundle total spaces is a local
biholomorphism, not merely a holomorphic fibrewise linear bijection. -/
theorem forwardMap_isLocalDiffeomorph {f : M → N}
    (hf : IsLocalDiffeomorph I I ω f) :
    IsLocalDiffeomorph Iᴷ Iᴷ ω (forwardMap hf) := by
  intro p
  let i : atlas Model M := achart Model p.proj
  let j : atlas Model N := achart Model (f p.proj)
  let a : M → ℂ := fun x => (chartDeterminant f i j x)⁻¹
  have hi : p.proj ∈ i.val.source := mem_chart_source Model p.proj
  have hj : f p.proj ∈ j.val.source := mem_chart_source Model (f p.proj)
  have hU : i.val.source ∩ f ⁻¹' j.val.source ∈ 𝓝 p.proj :=
    (i.val.open_source.inter (j.val.open_source.preimage hf.contMDiff.continuous)).mem_nhds
      ⟨hi, hj⟩
  have hdet : ContMDiffAt I I₁ ω (chartDeterminant f i j) p.proj :=
    (chartDeterminant_holomorphicOn f i j hf.contMDiff).contMDiffAt hU
  have hd : chartDeterminant f i j p.proj ≠ 0 :=
    chartDeterminant_ne_zero f i j hi hj (hf p.proj)
  have ha : ContMDiffAt I I₁ ω a p.proj := hdet.inv₀ hd
  have han : a p.proj ≠ 0 := inv_ne_zero hd
  have hs := localTriv_isLocalDiffeomorphAt i hi
  have hw : IsLocalDiffeomorphAt Iᴷ Iᴷ ω (weightedMap f a)
      ((Atlas.core M).localTriv i p) :=
    weightedMap_isLocalDiffeomorphAt (hf p.proj) ha han
  have ht : IsLocalDiffeomorphAt Iᴷ Iᴷ ω
      ((Atlas.core N).localTriv j).toOpenPartialHomeomorph.symm
      (weightedMap f a ((Atlas.core M).localTriv i p)) :=
    localTriv_symm_isLocalDiffeomorphAt j hj
  have hfirst := hs.comp (K := Iᴷ) (P := N × ℂ) hw
  have hall := hfirst.comp (K := Iᴷ) (P := (Atlas.core N).TotalSpace) ht
  apply localDiffeomorphAt_congr hall
  have hproj : ContinuousAt
      (Bundle.TotalSpace.proj : (Atlas.core M).TotalSpace → M) p :=
    (Bundle.contMDiffAt_proj (Atlas.core M).Fiber
      (IB := I) (n := ω)).continuousAt
  filter_upwards [hproj.preimage_mem_nhds hU] with q hq
  exact forwardMap_eq_localTriv_weighted hf i j q hq.1 hq.2

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
