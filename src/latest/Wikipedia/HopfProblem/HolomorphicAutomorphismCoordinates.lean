import Wikipedia.HopfProblem.HolomorphicAutomorphismTopology
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Compact-open convergence in original coordinate charts

For a fixed compact subset of an original chart target, every
automorphism sufficiently close to the identity maps its inverse image
back into the chart source. The literal coordinate expressions then
converge uniformly to the identity. This retains the ordinary topology
on the full automorphism group.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]

namespace Coordinates

variable (e : OpenPartialHomeomorph M E)

/-- The literal original-chart expression, with no regularity assertion
away from the region where both chart maps apply. -/
def expression (f : HolomorphicAutomorphism I M) (z : E) : E := e (f (e.symm z))

/-- The actual compact-open condition ensuring a coordinate expression
is defined on the given set in the original chart target. -/
def goodMaps (K : Set E) : Set (HolomorphicAutomorphism I M) :=
  {f | MapsTo f (e.symm '' K) e.source}

theorem isOpen_goodMaps {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target) :
    IsOpen (goodMaps (I := I) e K) := by
  have himage : IsCompact (e.symm '' K) := hK.image_of_continuousOn
    (e.symm.continuousOn.mono hKt)
  exact (ContinuousMap.isOpen_setOfPred_mapsTo himage e.open_source).preimage
    (continuous_toContinuousMap I M)

theorem one_mem_goodMaps {K : Set E} (hKt : K ⊆ e.target) :
    (1 : HolomorphicAutomorphism I M) ∈ goodMaps e K := by
  rintro _ ⟨z, hz, rfl⟩
  exact e.map_target (hKt hz)

theorem eventually_goodMaps {α : Type*} {l : Filter α}
    {f : α → HolomorphicAutomorphism I M} (hf : Tendsto f l (𝓝 1))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target) :
    ∀ᶠ n in l, f n ∈ goodMaps e K :=
  hf.eventually ((isOpen_goodMaps e hK hKt).mem_nhds (one_mem_goodMaps e hKt))

variable [LocallyCompactSpace M]

theorem expression_joint_continuousOn {K : Set E} (hKt : K ⊆ e.target) :
    ContinuousOn (fun p : HolomorphicAutomorphism I M × E => expression e p.1 p.2)
      (goodMaps e K ×ˢ K) := by
  have hi : ContinuousOn
      (fun p : HolomorphicAutomorphism I M × E => e.symm p.2) (goodMaps e K ×ˢ K) :=
    e.symm.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hKt hp.2)
  have hm : ContinuousOn
      (fun p : HolomorphicAutomorphism I M × E => p.1 (e.symm p.2))
      (goodMaps e K ×ˢ K) :=
    (continuous_eval I M).comp_continuousOn (continuous_fst.continuousOn.prodMk hi)
  exact e.continuousOn.comp hm (fun p hp => hp.1 ⟨p.2, hp.2, rfl⟩)

theorem expression_continuousOn {K : Set E} (hKt : K ⊆ e.target)
    {f : HolomorphicAutomorphism I M} (hf : f ∈ goodMaps e K) :
    ContinuousOn (expression e f) K :=
  (expression_joint_continuousOn e hKt).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ hz => ⟨hf, hz⟩)

/-- A total continuous-map-valued expression. Its default is used only
outside the coordinate-valid region and disappears near the identity. -/
def restrictedExpression (K : Set E) (f : HolomorphicAutomorphism I M) : C(K, E) :=
  ContinuousMap.mkD (K.domRestrict (expression e f)) ⟨Subtype.val, continuous_subtype_val⟩

theorem restrictedExpression_apply {K : Set E} (hKt : K ⊆ e.target)
    {f : HolomorphicAutomorphism I M} (hf : f ∈ goodMaps e K) (z : K) :
    restrictedExpression e K f z = expression e f z := by
  exact ContinuousMap.mkD_apply_of_continuousOn (expression_continuousOn e hKt hf)

theorem restrictedExpression_continuousAt_one {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ e.target) :
    ContinuousAt (restrictedExpression (I := I) e K) 1 := by
  have h : ContinuousOn (restrictedExpression (I := I) e K) (goodMaps e K) :=
    ContinuousMap.continuousOn_mkD_restrict_of_uncurry (expression e)
      ⟨Subtype.val, continuous_subtype_val⟩ (expression_joint_continuousOn e hKt)
  exact h.continuousAt ((isOpen_goodMaps e hK hKt).mem_nhds (one_mem_goodMaps e hKt))

omit [LocallyCompactSpace M] in
@[simp] theorem expression_one {z : E} (hz : z ∈ e.target) :
    expression e (1 : HolomorphicAutomorphism I M) z = z := e.right_inv hz

/-- Compact-open convergence of the genuine automorphisms implies
uniform convergence of their actual coordinate expressions on every
compact subset of the chart target. -/
theorem tendstoUniformlyOn_expression {α : Type*} {l : Filter α}
    {f : α → HolomorphicAutomorphism I M} (hf : Tendsto f l (𝓝 1))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ e.target) :
    TendstoUniformlyOn (fun n => expression e (f n)) id l K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hconv : Tendsto (fun n => restrictedExpression e K (f n)) l
      (𝓝 (restrictedExpression e K 1)) :=
    (restrictedExpression_continuousAt_one e hK hKt).tendsto.comp hf
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hconv
  have he : ∀ᶠ n in l, ∀ z : K,
      restrictedExpression e K (f n) z = expression e (f n) z :=
    (eventually_goodMaps e hf hK hKt).mono fun _ hn z =>
      restrictedExpression_apply e hKt hn z
  have hone : ∀ z : K, restrictedExpression (I := I) e K 1 z = (z : E) := by
    intro z
    rw [restrictedExpression_apply e hKt (one_mem_goodMaps (I := I) e hKt),
      expression_one (I := I) e (hKt z.2)]
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  intro V hV
  filter_upwards [hu V hV, he] with n hn hne z
  simpa only [hne z, hone z, Function.comp_def, id_eq] using hn z

end Coordinates

end Wikipedia.HopfProblem.HolomorphicAutomorphism
