import Wikipedia.HopfProblem.HolomorphicAutomorphismBasic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction

/-!
# The compact-open topology on native holomorphic automorphisms

The topology is induced by the pair consisting of an automorphism and
its inverse, both viewed as continuous maps with the compact-open topology.
For a locally compact manifold, this makes the native automorphism group
a topological group with continuous joint evaluation. Its identity
component is the connected component of the identity in this topology.
-/

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism

private theorem compact_inverse_family {X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] [CompactSpace M] [T2Space M] {f g : X → C(M, M)}
    (hleft : ∀ x y, g x (f x y) = y) (hright : ∀ x y, f x (g x y) = y)
    (hf : Continuous f) : Continuous g := by
  classical
  apply ContinuousMap.continuous_compactOpen.mpr
  intro K hK U hU
  have he : {x | MapsTo (g x) K U} = {x | MapsTo (f x) Uᶜ Kᶜ} := by
    ext x
    change MapsTo (g x) K U ↔ MapsTo (f x) Uᶜ Kᶜ
    constructor
    · intro hx y hy hyK
      have hu := hx hyK
      rw [hleft x y] at hu
      exact hy hu
    · intro hx y hy
      by_contra hnot
      have hnotK := hx hnot
      rw [hright x y] at hnotK
      exact hnotK hy
  rw [he]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hU.isClosed_compl.isCompact
    hK.isClosed.isOpen_compl).preimage hf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M]

/-- Simultaneous compact-open convergence of the native forward and inverse maps. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (HolomorphicAutomorphism I M) :=
  TopologicalSpace.induced toPair inferInstance

theorem continuous_toPair :
    Continuous (toPair : HolomorphicAutomorphism I M → C(M, M) × C(M, M)) :=
  continuous_induced_dom

theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : HolomorphicAutomorphism I M → C(M, M)) :=
  (continuous_toPair I M).fst

theorem continuous_inverseContinuousMap :
    Continuous (fun f : HolomorphicAutomorphism I M => (f⁻¹).toContinuousMap) :=
  (continuous_toPair I M).snd

/-- Continuity into the automorphism group is exactly continuity of both
compact-open components; neither component is discarded. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → HolomorphicAutomorphism I M} :
    Continuous f ↔
      Continuous (fun x => (f x).toContinuousMap) ∧
      Continuous (fun x => ((f x)⁻¹).toContinuousMap) := by
  constructor
  · intro hf
    exact ⟨(continuous_toContinuousMap I M).comp hf,
      (continuous_inverseContinuousMap I M).comp hf⟩
  · rintro ⟨hf, hi⟩
    exact continuous_induced_rng.mpr (hf.prodMk hi)

/-- On a compact Hausdorff manifold, compact-open continuity of the
forward maps already forces compact-open continuity of their inverses. -/
theorem continuous_iff_toContinuousMap_of_compact [CompactSpace M] [T2Space M]
    {X : Type*} [TopologicalSpace X] {f : X → HolomorphicAutomorphism I M} :
    Continuous f ↔ Continuous (fun x => (f x).toContinuousMap) := by
  rw [continuous_iff I M]
  constructor
  · exact And.left
  · intro hf
    refine ⟨hf, compact_inverse_family ?_ ?_ hf⟩
    · intro x y
      exact inv_apply_apply (f x) y
    · intro x y
      exact apply_inv_apply (f x) y

/-- On a compact Hausdorff manifold, the group topology is precisely the
topology induced by the forward compact-open map alone. -/
theorem isInducing_toContinuousMap_of_compact [CompactSpace M] [T2Space M] :
    IsInducing (toContinuousMap : HolomorphicAutomorphism I M → C(M, M)) where
  eq_induced := by
    apply le_antisymm
    · exact continuous_iff_le_induced.mp (continuous_toContinuousMap I M)
    · let tfwd : TopologicalSpace (HolomorphicAutomorphism I M) :=
        TopologicalSpace.induced toContinuousMap inferInstance
      have h : @Continuous (HolomorphicAutomorphism I M) (HolomorphicAutomorphism I M)
          tfwd (instTopologicalSpace I M) id := by
        let : TopologicalSpace (HolomorphicAutomorphism I M) := tfwd
        apply (continuous_iff_toContinuousMap_of_compact I M).mpr
        exact continuous_induced_dom
      simpa only [induced_id] using continuous_iff_le_induced.mp h

/-- Thus the full native automorphism group has its ordinary forward
compact-open subspace topology when the manifold is compact Hausdorff. -/
theorem isEmbedding_toContinuousMap_of_compact [CompactSpace M] [T2Space M] :
    IsEmbedding (toContinuousMap : HolomorphicAutomorphism I M → C(M, M)) :=
  ⟨isInducing_toContinuousMap_of_compact I M, toContinuousMap_injective⟩

/-- The automorphism group embeds in the product of its two continuous-map spaces. -/
theorem isEmbedding_toPair :
    IsEmbedding (toPair : HolomorphicAutomorphism I M → C(M, M) × C(M, M)) where
  eq_induced := rfl
  injective := toPair_injective

instance instT2Space [T2Space M] : T2Space (HolomorphicAutomorphism I M) :=
  (isEmbedding_toPair I M).t2Space

/-- Inversion exchanges the forward and inverse compact-open components. -/
instance instContinuousInv : ContinuousInv (HolomorphicAutomorphism I M) where
  continuous_inv := by
    apply (continuous_iff I M).mpr
    refine ⟨continuous_inverseContinuousMap I M, ?_⟩
    simpa only [inv_inv] using continuous_toContinuousMap I M

instance instIsTopologicalGroup [LocallyCompactSpace M] :
    IsTopologicalGroup (HolomorphicAutomorphism I M) where
  toContinuousInv := inferInstance
  continuous_mul := by
    apply (continuous_iff I M).mpr
    constructor
    · have h : Continuous (fun p : HolomorphicAutomorphism I M × HolomorphicAutomorphism I M =>
          p.1.toContinuousMap.comp p.2.toContinuousMap) :=
        ((continuous_toContinuousMap I M).comp continuous_fst).compCM
          ((continuous_toContinuousMap I M).comp continuous_snd)
      simpa only [toContinuousMap_mul] using h
    · have h : Continuous (fun p : HolomorphicAutomorphism I M × HolomorphicAutomorphism I M =>
          (p.2⁻¹).toContinuousMap.comp (p.1⁻¹).toContinuousMap) :=
        ((continuous_inverseContinuousMap I M).comp continuous_snd).compCM
          ((continuous_inverseContinuousMap I M).comp continuous_fst)
      simpa only [mul_inv_rev, toContinuousMap_mul] using h

/-- Joint evaluation uses the original action of each native automorphism on the manifold. -/
theorem continuous_eval [LocallyCompactSpace M] :
    Continuous (fun p : HolomorphicAutomorphism I M × M => p.1 p.2) := by
  have h : Continuous (fun p : HolomorphicAutomorphism I M × M =>
      (p.1.toContinuousMap, p.2)) :=
    ((continuous_toContinuousMap I M).comp continuous_fst).prodMk continuous_snd
  exact (show Continuous (fun p : C(M, M) × M => p.1 p.2) from
    ContinuousEval.continuous_eval).comp h

instance instContinuousSMul [LocallyCompactSpace M] :
    ContinuousSMul (HolomorphicAutomorphism I M) M where
  continuous_smul := continuous_eval I M

/-- The identity component of the native holomorphic automorphism group
for the simultaneous forward-and-inverse compact-open topology. -/
noncomputable def identityComponent [LocallyCompactSpace M] :
    Subgroup (HolomorphicAutomorphism I M) :=
  Subgroup.connectedComponentOfOne (HolomorphicAutomorphism I M)

theorem mem_identityComponent_iff [LocallyCompactSpace M]
    (f : HolomorphicAutomorphism I M) :
    f ∈ identityComponent I M ↔
      f ∈ connectedComponent (1 : HolomorphicAutomorphism I M) := Iff.rfl

end Wikipedia.HopfProblem.HolomorphicAutomorphism
