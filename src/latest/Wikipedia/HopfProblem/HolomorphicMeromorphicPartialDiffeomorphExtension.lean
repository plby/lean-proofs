import Wikipedia.HopfProblem.HolomorphicMeromorphicPartialDiffeomorphNaturality
import Wikipedia.HopfProblem.HolomorphicMeromorphicScalar
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Transferring scalar meromorphic extension through a genuine partial chart

Scalar meromorphy at the chart center supplies a native local section.
Transporting it back on the inverse image of a small connected ball gives
an actual connected manifold neighborhood. Punctured scalar agreement
detects equality of the full original meromorphic germs at an overlap point.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PartialBiholomorph

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- A scalar meromorphic extension in the actual partial chart supplies
a genuine native meromorphic section on a connected neighborhood of its
center, with full-germ agreement at an actual point of the old domain. -/
theorem exists_connected_extension_of_scalar_meromorphicAt
    (e : PartialDiffeomorph I 𝓘(ℂ) M ℂ ω) (U : Opens M) (s : Section I M U)
    (b : M) (hb : b ∈ e.source) (he0 : e b = 0)
    (hdomain : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ e.target ∧ e.symm t ∈ U)
    (hmero : MeromorphicAt (scalarValue (transportSection I 𝓘(ℂ) e U s)) 0) :
    ∃ (W : Opens M), b ∈ W ∧ IsConnected (W : Set M) ∧
      (W : Set M) ⊆ e.source ∧
      ∃ (a : Section I M W) (y : M) (hyW : y ∈ W) (hyU : y ∈ U),
        a ⟨y, hyW⟩ = s ⟨y, hyU⟩ := by
  obtain ⟨V, h0V, aV, hagree⟩ := exists_section_of_meromorphicAt hmero
  have h0target : (0 : ℂ) ∈ e.target :=
    (congrArg (fun t : ℂ => t ∈ e.target) he0).mp (e.map_source hb)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (V.isOpen.inter e.open_target)
    0 ⟨h0V, h0target⟩
  let B : Opens ℂ := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have h0B : (0 : ℂ) ∈ B := Metric.mem_ball_self hr
  have hBV : B ≤ V := fun _ ht => (hball ht).1
  have hBt : (B : Set ℂ) ⊆ e.target := fun _ ht => (hball ht).2
  let aB := restrict 𝓘(ℂ) ℂ hBV aV
  let W := transportOpen 𝓘(ℂ) I e.symm B
  have hbW : b ∈ W :=
    ⟨hb, (congrArg (fun t : ℂ => t ∈ B) he0).mpr h0B⟩
  have hWsource : (W : Set M) ⊆ e.source := fun _ hx => hx.1
  have hWimage : (W : Set M) = e.symm '' (B : Set ℂ) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx.2, e.left_inv hx.1⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨e.map_target (hBt ht),
        (congrArg (fun z : ℂ => z ∈ B) (e.right_inv (hBt ht))).mpr ht⟩
  have hWconnected : IsConnected (W : Set M) :=
    (congrArg IsConnected hWimage).mpr
      ((Metric.isConnected_ball hr).image e.symm (e.contMDiffOn_invFun.continuousOn.mono hBt))
  let a := transportSection 𝓘(ℂ) I e.symm B aB
  have hlocal : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      scalarValue aV =ᶠ[𝓝[{0}ᶜ] t] scalarValue (transportSection I 𝓘(ℂ) e U s) :=
    eventually_eventually_nhdsWithin.mpr hagree
  have hchoose : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ B ∧
      (t ∈ e.target ∧ e.symm t ∈ U) ∧
      scalarValue aV =ᶠ[𝓝 t] scalarValue (transportSection I 𝓘(ℂ) e U s) := by
    filter_upwards [nhdsWithin_le_nhds (B.isOpen.mem_nhds h0B), hdomain,
      self_mem_nhdsWithin, hlocal] with t htB htU htne hteq
    refine ⟨htB, htU, ?_⟩
    exact (isOpen_compl_singleton.nhdsWithin_eq htne) ▸ hteq
  obtain ⟨t, htB, htU, hteq⟩ := hchoose.exists
  have htgt : t ∈ e.symm.source := htU.1
  let yW := transportPoint 𝓘(ℂ) I e.symm B ⟨t, htB⟩ htgt
  have hgen : aB ⟨t, htB⟩ = transportSection I 𝓘(ℂ) e U s ⟨t, htU⟩ :=
    germ_eq_of_scalarValue_eventuallyEq aV (transportSection I 𝓘(ℂ) e U s)
      t (hBV htB) htU (hteq.filter_mono nhdsWithin_le_nhds)
  refine ⟨W, hbW, hWconnected, hWsource, a, e.symm t, yW.property, htU.2, ?_⟩
  apply (germEquiv 𝓘(ℂ) I e.symm t htgt).injective
  exact (germEquiv_transportSection 𝓘(ℂ) I e.symm B aB ⟨t, htB⟩ htgt).trans hgen

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PartialBiholomorph
