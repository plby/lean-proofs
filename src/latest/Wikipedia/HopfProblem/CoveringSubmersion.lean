import Wikipedia.HopfProblem.CuspPuncturedCovering
import Mathlib.Geometry.Manifold.Submersion

/-!
# Submersions in commuting squares of holomorphic coverings

Local biholomorphisms transport the actual projection normal form of a
submersion.  The domain chart is restricted so that its image is contained
in one inverse branch of the map on the base.  Applying this to the
constructed covering-quotient atlases proves descent of submersions.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

section LocalDiffeomorphSquare

variable {E E' F M M' N N' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace M'] [ChartedSpace E M']
    [TopologicalSpace N] [ChartedSpace E' N]
    [TopologicalSpace N'] [ChartedSpace E' N']
    [IsManifold (modelWithCornersSelf ℂ E) ω M']
    [IsManifold (modelWithCornersSelf ℂ E') ω N']

/-- A commuting square whose horizontal maps are locally biholomorphic
preserves the full submersion normal form, with the same complement. -/
theorem submersionAt_of_localDiffeomorph_square
    {qM : M → M'} {qN : N → N'} {f : M → N} {f' : M' → N'} {x : M}
    (hqM : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω qM x)
    (hqN : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E')
      (modelWithCornersSelf ℂ E') ω qN (f x))
    (hf : Manifold.IsSubmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f x)
    (hsquare : ∀ y, f' (qM y) = qN (f y)) :
    Manifold.IsSubmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f' (qM x) := by
  obtain ⟨p, hp, hqp⟩ := hqM
  obtain ⟨r, hr, hqr⟩ := hqN
  let e := p.toOpenPartialHomeomorph
  let t := r.toOpenPartialHomeomorph
  change EqOn qM e e.source at hqp
  change EqOn qN t t.source at hqr
  have hpre : f ⁻¹' t.source ∈ 𝓝 x :=
    hf.contMDiffAt.continuousAt (t.open_source.mem_nhds hr)
  obtain ⟨U, hUf, hU, hxU⟩ := mem_nhds_iff.mp hpre
  let d₀ := hf.domChart.restr U
  let d := e.symm.trans d₀
  let c := t.symm.trans hf.codChart
  have hd₀ : d₀ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ E) ω M :=
    restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hU
  have hx₀ : x ∈ d₀.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ hU]
    exact ⟨hf.mem_domChart_source, hxU⟩
  have hx : qM x ∈ d.source := by
    change qM x ∈ e.target ∧ e.symm (qM x) ∈ d₀.source
    rw [hqp hp]
    exact ⟨e.map_source hp, by simpa only [e.left_inv hp] using hx₀⟩
  have hsource : d.source ⊆ f' ⁻¹' c.source := by
    intro y hy
    have hy₀ : e.symm y ∈ d₀.source := hy.2
    rw [OpenPartialHomeomorph.restr_source' _ _ hU] at hy₀
    have hfy : f (e.symm y) ∈ t.source := hUf hy₀.2
    have hval : f' y = t (f (e.symm y)) := by
      calc
        f' y = f' (qM (e.symm y)) :=
          congrArg f' ((hqp (e.map_target hy.1)).trans (e.right_inv hy.1)).symm
        _ = qN (f (e.symm y)) := hsquare _
        _ = t (f (e.symm y)) := hqr hfy
    change f' y ∈ t.target ∧ t.symm (f' y) ∈ hf.codChart.source
    rw [hval, t.left_inv hfy]
    exact ⟨t.map_source hfy, hf.source_subset_preimage_source hy₀.1⟩
  refine Manifold.IsSubmersionAtOfComplement.mk_of_charts hf.equiv d c hx
    (hsource hx) ?_ ?_ hsource ?_
  · apply d.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hd₀).comp
        (p.contMDiffOn_invFun.mono inter_subset_left) (fun _ hy => hy.2)
    · exact p.contMDiffOn_toFun.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hd₀).mono inter_subset_left)
        (fun _ hy => hy.2)
  · apply c.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
        (r.contMDiffOn_invFun.mono inter_subset_left) (fun _ hy => hy.2)
    · exact r.contMDiffOn_toFun.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).mono
          inter_subset_left) (fun _ hy => hy.2)
  · intro z hz
    have hz' : z ∈ d.target := by simpa [OpenPartialHomeomorph.extend] using hz
    have hu : hf.domChart.symm z ∈ d₀.source := d₀.map_target hz'.1
    rw [OpenPartialHomeomorph.restr_source' _ _ hU] at hu
    have hfu : f (hf.domChart.symm z) ∈ t.source := hUf hu.2
    have hqe : qM (hf.domChart.symm z) = e (hf.domChart.symm z) := hqp hz'.2
    change hf.codChart (t.symm (f' (e (hf.domChart.symm z)))) = (hf.equiv z).1
    rw [← hqe, hsquare, hqr hfu, t.left_inv hfu]
    exact hf.writtenInCharts (by
      simpa [OpenPartialHomeomorph.extend] using hz'.1.1)

/-- The global version of submersion descent through a commuting square
of local biholomorphisms.  Only the map on the total spaces must be onto. -/
theorem submersion_of_localDiffeomorph_square
    {qM : M → M'} {qN : N → N'} {f : M → N} {f' : M' → N'}
    (hqM : IsLocalDiffeomorph (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω qM)
    (hqN : IsLocalDiffeomorph (modelWithCornersSelf ℂ E')
      (modelWithCornersSelf ℂ E') ω qN)
    (hsurj : Function.Surjective qM)
    (hf : Manifold.IsSubmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f)
    (hsquare : ∀ y, f' (qM y) = qN (f y)) :
    Manifold.IsSubmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f' := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact submersionAt_of_localDiffeomorph_square (hqM x) (hqN (f x)) (hf x) hsquare

end LocalDiffeomorphSquare

namespace CoveringQuotient

variable {E E' F M Q N R G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
    [TopologicalSpace N] [ChartedSpace E' N] [TopologicalSpace R]
    [Group G] [MulAction G M] [Group H] [MulAction H N]
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    [IsManifold (modelWithCornersSelf ℂ E') ω N]
    {qM : M → Q} {qN : N → R}
    (hqM : IsQuotientCoveringMap qM G) (hqN : IsQuotientCoveringMap qN H)
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    (hH : ∀ g : H, ContMDiff (modelWithCornersSelf ℂ E')
      (modelWithCornersSelf ℂ E') ω (fun x : N => g • x))

include hG hH

/-- Pointwise descent to the actual analytic covering-quotient atlases. -/
theorem submersionAt_descend {f : M → N} {f' : Q → R} {x : M}
    (hf : Manifold.IsSubmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f x)
    (hsquare : ∀ y, f' (qM y) = qN (f y)) :
    letI := chartedSpace (E := E) hqM
    letI := chartedSpace (E := E') hqN
    Manifold.IsSubmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f' (qM x) := by
  let := chartedSpace (E := E) hqM
  let := chartedSpace (E := E') hqN
  let := isManifold hqM ω hG
  let := isManifold hqN ω hH
  exact submersionAt_of_localDiffeomorph_square
    (project_isLocalDiffeomorph hqM hG x) (project_isLocalDiffeomorph hqN hH (f x))
    hf hsquare

/-- A submersion equivariant over two holomorphic covering quotients
descends to a submersion, preserving its complement. -/
theorem submersion_descend {f : M → N} {f' : Q → R}
    (hf : Manifold.IsSubmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f)
    (hsquare : ∀ y, f' (qM y) = qN (f y)) :
    letI := chartedSpace (E := E) hqM
    letI := chartedSpace (E := E') hqN
    Manifold.IsSubmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f' := by
  let := chartedSpace (E := E) hqM
  let := chartedSpace (E := E') hqN
  intro y
  obtain ⟨x, rfl⟩ := hqM.surjective y
  exact submersionAt_descend hqM hqN hG hH (hf x) hsquare

end CoveringQuotient

end Wikipedia.HopfProblem
