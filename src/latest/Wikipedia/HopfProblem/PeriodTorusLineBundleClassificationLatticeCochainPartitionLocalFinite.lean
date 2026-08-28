import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochainPartitionGeometry
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Local finiteness of actual period-lattice translates

The actual period lattice is closed and discrete.  A compact set therefore
contains only finitely many lattice points.  If a translated compact set
meets a fixed small ball, its translating lattice point belongs to a
compact difference set.  This proves local finiteness without any
assumed fundamental-domain finiteness or support condition beyond compact
support of the original function.
-/

noncomputable section

open Set Metric Function
open scoped Topology

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain

/-- A compact subset of the actual cover contains only finitely many
points of the actual period lattice. -/
theorem finite_lattice_preimage_of_isCompact (p : PeriodDomain)
    {K : Set ComplexPlane₂} (hK : IsCompact K) :
    Set.Finite {l : p.lattice | (l : ComplexPlane₂) ∈ K} := by
  let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
  exact (p.lattice_isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    hK).finite_of_discrete

/-- Preimages of a compact set under translation by actual lattice
points form a locally finite family. -/
theorem locallyFinite_lattice_compact_preimages (p : PeriodDomain)
    {K : Set ComplexPlane₂} (hK : IsCompact K) :
    LocallyFinite (fun l : p.lattice =>
      (fun z : ComplexPlane₂ => z + (l : ComplexPlane₂)) ⁻¹' K) := by
  intro x
  let C : Set ComplexPlane₂ :=
    (fun q : ComplexPlane₂ × ComplexPlane₂ => q.1 - q.2) ''
      (K ×ˢ closedBall x 1)
  have hC : IsCompact C :=
    (hK.prod (isCompact_closedBall x 1)).image
      (continuous_fst.sub continuous_snd)
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (finite_lattice_preimage_of_isCompact p hC).subset ?_⟩
  intro l hl
  obtain ⟨y, hy, hyx⟩ := hl
  refine ⟨(y + (l : ComplexPlane₂), y),
    ⟨hy, ball_subset_closedBall hyx⟩, ?_⟩
  dsimp only
  abel

/-- The topological supports of lattice translates of an arbitrary
compactly supported real function are locally finite. -/
theorem locallyFinite_lattice_translates (p : PeriodDomain)
    {χ : ComplexPlane₂ → ℝ} (hχ : HasCompactSupport χ) :
    LocallyFinite (fun l : p.lattice =>
      tsupport (fun z : ComplexPlane₂ => χ (z + (l : ComplexPlane₂)))) := by
  apply (locallyFinite_lattice_compact_preimages p hχ).subset
  intro l
  exact tsupport_comp_subset_preimage χ (continuous_id.add continuous_const)

/-- At any point, only finitely many lattice translates of the cutoff
have nonzero value. -/
theorem hasFiniteSupport_lattice_translates (p : PeriodDomain)
    {χ : ComplexPlane₂ → ℝ} (hχ : HasCompactSupport χ) (z : ComplexPlane₂) :
    HasFiniteSupport (fun l : p.lattice => χ (z + (l : ComplexPlane₂))) := by
  exact ((locallyFinite_lattice_translates p hχ).point_finite z).subset
    (fun l hl => subset_tsupport (fun w : ComplexPlane₂ => χ (w + (l : ComplexPlane₂))) hl)

/-- The pointwise lattice sum of a compactly supported cutoff is an
ordinary finitely supported, hence summable, family. -/
theorem summable_lattice_translates (p : PeriodDomain)
    {χ : ComplexPlane₂ → ℝ} (hχ : HasCompactSupport χ) (z : ComplexPlane₂) :
    Summable (fun l : p.lattice => χ (z + (l : ComplexPlane₂))) :=
  summable_of_hasFiniteSupport (hasFiniteSupport_lattice_translates p hχ z)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
