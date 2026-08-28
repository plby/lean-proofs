import Wikipedia.SmoothSixDPoincare.NativeSubmersionStability
import Wikipedia.SmoothSixDPoincare.ChartTransversalityPerturbation

/-!
# Compact stability of transversality for native smooth sheets

At a crossing, a common target chart detects transversality by the surjective
derivative of the difference map. Away from a crossing, disjointness persists
by continuity. These two open conditions give uniform stability on compact
sets of source pairs, including pairs which initially do not intersect.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.NativeTransversality

variable {D Z G H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]
  [TopologicalSpace N] [ChartedSpace K N]

variable (I I' J) in
/-- The native tangent maps span at a crossing; noncrossing source pairs impose no condition. -/
def At (f : X → N) (g : Y → N) (x : X) (y : Y) : Prop :=
  g y = f x → Surjective ((mfderiv I J f x : D →L[ℝ] G).coprod
    (mfderiv I' J g y : Z →L[ℝ] G))

/-- At an actual crossing, a common chart identifies transversality with a submersion. -/
theorem at_iff_chart_difference {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hxy : g y = f x) (hx : f x ∈ c.source) :
    At I I' J f g x y ↔ Surjective (mfderiv (I.prod I') 𝓘(ℝ, F)
      (fun z : X × Y => c (g z.2) - c (f z.1)) (x, y)) := by
  have hy : g y ∈ c.source := hxy ▸ hx
  have hcf := (c.mdifferentiableAt (by simp) hx).comp x hf
  have hcg := (c.mdifferentiableAt (by simp) hy).comp y hg
  have hdiff := TransverseCoordinates.surjective_sheetDifference_iff hcf hcg
  constructor
  · intro ht
    apply hdiff.mpr
    exact ChartMapPerturbation.transverse_in_chart c hf hg hxy hx (ht hxy)
  · intro h _
    exact ChartMapPerturbation.transverse_of_chart c hf hg hxy hx (hdiff.mp h)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ G]
  [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [IsManifold I ∞ X] [IsManifold I' ∞ Y] [IsManifold J ∞ N] [T2Space N]

/-- Transversality of one smoothly varying sheet to a fixed sheet is an open condition
in the parameter and both source points, for complementary dimensions. -/
theorem isOpen_at_family {f : P → X → N} {g : Y → N} {U : Set P}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (uncurry f) (U ×ˢ univ))
    (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) :
    IsOpen {r : P × (X × Y) | r.1 ∈ U ∧ At I I' J (f r.1) g r.2.1 r.2.2} := by
  let W₀ : Set (P × (X × Y)) := U ×ˢ univ
  have hW₀ : IsOpen W₀ := hU.prod isOpen_univ
  let F : P × (X × Y) → N := fun r => f r.1 r.2.1
  let G' : P × (X × Y) → N := fun r => g r.2.2
  have hF : ContMDiffOn (𝓘(ℝ, P).prod (I.prod I')) J ∞ F W₀ :=
    hf.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).contMDiffOn
      (fun _ hr => ⟨hr.1, mem_univ _⟩)
  have hG : ContMDiff (𝓘(ℝ, P).prod (I.prod I')) J ∞ G' :=
    hg.comp (contMDiff_snd.comp contMDiff_snd)
  have hslice (a : P) (x : X) (ha : a ∈ U) : ContMDiffAt I J ∞ (f a) x :=
    (hf.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ha, mem_univ x⟩)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hq, hqt⟩
  have hq₀ : q ∈ W₀ := ⟨hq, mem_univ _⟩
  by_cases hcross : g q.2.2 = f q.1 q.2.1
  · let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f q.1 q.2.1)
    have hqc : f q.1 q.2.1 ∈ c.source := mem_extChartAt_source _
    have hqgc : g q.2.2 ∈ c.source := hcross ▸ hqc
    let W : Set (P × (X × Y)) := (W₀ ∩ F ⁻¹' c.source) ∩ G' ⁻¹' c.source
    have hW : IsOpen W :=
      (hF.continuousOn.isOpen_inter_preimage hW₀ c.open_source).inter
        (c.open_source.preimage hG.continuous)
    let B : P → X × Y → G := fun a z => c (g z.2) - c (f a z.1)
    have hB : ContMDiffOn (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞ (uncurry B) W := by
      intro r hr
      have hfirst : ContMDiffAt (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞
          (fun s : P × (X × Y) => c (f s.1 s.2.1)) r :=
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.1.2)).comp r
          (hF.contMDiffAt (hW₀.mem_nhds hr.1.1))
      have hsecond : ContMDiffAt (𝓘(ℝ, P).prod (I.prod I')) 𝓘(ℝ, G) ∞
          (fun s : P × (X × Y) => c (g s.2.2)) r :=
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hr.2)).comp r
          hG.contMDiffAt
      exact (hsecond.sub hfirst).contMDiffWithinAt
    have hopen := NativeSubmersion.isOpen_surjective_nativeDerivative hW hB
      (by simpa only [Module.finrank_prod] using hdim)
    have hqB : Surjective (mfderiv (I.prod I') 𝓘(ℝ, G) (B q.1) q.2) :=
      (at_iff_chart_difference c ((hslice q.1 q.2.1 hq).mdifferentiableAt (by simp))
        (hg.mdifferentiableAt (by simp)) hcross hqc).mp hqt
    have hn := hopen.mem_nhds (show q ∈ {r | r ∈ W ∧
        Surjective (mfderiv (I.prod I') 𝓘(ℝ, G) (B r.1) r.2)} from
      ⟨⟨⟨hq₀, hqc⟩, hqgc⟩, hqB⟩)
    apply mem_of_superset hn
    intro r hr
    refine ⟨hr.1.1.1.1, ?_⟩
    intro hxy
    have ht := (at_iff_chart_difference c
      ((hslice r.1 r.2.1 hr.1.1.1.1).mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp)) hxy hr.1.1.2).mpr hr.2
    exact ht hxy
  · have hpair : ContinuousAt (fun r : P × (X × Y) => (G' r, F r)) q :=
      hG.continuous.continuousAt.prodMk (hF.contMDiffAt (hW₀.mem_nhds hq₀)).continuousAt
    have hne : IsOpen {z : N × N | z.1 ≠ z.2} :=
      isOpen_ne_fun continuous_fst continuous_snd
    have hn := hpair.preimage_mem_nhds (hne.mem_nhds hcross)
    have hparam : ∀ᶠ r : P × (X × Y) in 𝓝 q, r.1 ∈ U :=
      continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hq)
    apply mem_of_superset (inter_mem hparam hn)
    intro r hr
    refine ⟨hr.1, ?_⟩
    intro hxy
    exact False.elim (hr.2 hxy)

/-- Every source pair in a compact set remains transverse after a sufficiently small
parameter change; initially disjoint pairs are included in this guarantee. -/
theorem eventually_on_compact {f : P → X → N} {g : Y → N} {U : Set P}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) J ∞ (uncurry f) (U ×ˢ univ))
    (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G)
    {C : Set (X × Y)} (hC : IsCompact C) {a : P} (ha : a ∈ U)
    (htrans : ∀ z ∈ C, At I I' J (f a) g z.1 z.2) :
    ∀ᶠ b in 𝓝 a, ∀ z ∈ C, At I I' J (f b) g z.1 z.2 := by
  have hopen := MorsePerturbation.isOpen_forall_mem_compact hC
    (isOpen_at_family hU hf hg hdim)
  have hn := hopen.mem_nhds (fun z hz => ⟨ha, htrans z hz⟩)
  filter_upwards [hn] with b hb z hz
  exact (hb z hz).2

end Wikipedia.SmoothSixDPoincare.NativeTransversality
