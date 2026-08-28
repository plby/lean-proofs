import Wikipedia.HopfProblem.HolomorphicMeromorphicSections
import Wikipedia.HopfProblem.HolomorphicMeromorphicIdentity

/-!
# Local equality and the identity principle for genuine meromorphic sections

Two local fractions are equal precisely when their holomorphic cross
product vanishes as a germ. The native holomorphic identity principle
therefore makes their equality locus clopen. Refining the actual local
presentations proves the same statement for arbitrary locally represented
meromorphic sections. In particular a meromorphic function on a connected
domain is determined by any one of its actual fraction germs.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- Equality of fraction germs is vanishing of the actual holomorphic
cross product, including at zeros of both local numerators. -/
theorem fraction_eq_iff_cross_germ_zero (U : Opens M)
    (p q r s : HolomorphicFunctionSheaf.Section I M U) (x : U)
    (hq : holomorphicGerm I M U x q ≠ 0) (hs : holomorphicGerm I M U x s ≠ 0) :
    fraction I M U p q x = fraction I M U r s x ↔
      holomorphicGerm I M U x (p * s - r * q) = 0 := by
  rw [fraction_eq_iff I M U p q r s x hq hs, map_sub, sub_eq_zero]

/-- The equality locus of genuine fractions is clopen in their actual domain. -/
theorem isClopen_fraction_eq (U : Opens M)
    (p q r s : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0)
    (hs : ∀ x : U, holomorphicGerm I M U x s ≠ 0) :
    IsClopen {x : U | fraction I M U p q x = fraction I M U r s x} := by
  have he : {x : U | fraction I M U p q x = fraction I M U r s x} =
      {x : U | (HolomorphicFunctionSheaf.presheaf I M).germ U x.val x.property
        (p * s - r * q) ≠ 0}ᶜ := by
    ext x
    change (fraction I M U p q x = fraction I M U r s x) ↔
      ¬ (holomorphicGerm I M U x (p * s - r * q) ≠ 0)
    rw [not_not]
    exact fraction_eq_iff_cross_germ_zero I M U p q r s x (hq x) (hs x)
  rw [he]
  exact (HolomorphicFunctionSheaf.isClopen_nonzero_germ_locus I U (p * s - r * q)).compl

/-- Two arbitrary sections admit fraction representatives on one common
actual neighborhood, obtained by restricting their original presentations. -/
theorem common_local_representation {U : Opens M} (a b : Section I M U) (x : U) :
    ∃ (V : Opens M) (hVU : V ≤ U) (_hxV : x.val ∈ V)
      (p q r s : HolomorphicFunctionSheaf.Section I M V),
      (∀ y : V, holomorphicGerm I M V y q ≠ 0) ∧
      (∀ y : V, holomorphicGerm I M V y s ≠ 0) ∧
      (∀ y : V, a (Set.inclusion hVU y) = fraction I M V p q y) ∧
        ∀ y : V, b (Set.inclusion hVU y) = fraction I M V r s y := by
  obtain ⟨V, hVU, hxV, p, q, hq, ha⟩ := local_representation I M a x
  obtain ⟨W, hWU, hxW, r, s, hs, hb⟩ := local_representation I M b x
  let T : Opens M := V ⊓ W
  have hTV : T ≤ V := inf_le_left
  have hTW : T ≤ W := inf_le_right
  have hTU : T ≤ U := hTV.trans hVU
  refine ⟨T, hTU, ⟨hxV, hxW⟩,
    HolomorphicFunctionSheaf.restrictionAlgHom I M hTV p,
    HolomorphicFunctionSheaf.restrictionAlgHom I M hTV q,
    HolomorphicFunctionSheaf.restrictionAlgHom I M hTW r,
    HolomorphicFunctionSheaf.restrictionAlgHom I M hTW s, ?_, ?_, ?_, ?_⟩
  · intro y hzero
    exact hq (Set.inclusion hTV y)
      ((holomorphicGerm_restrict I M hTV y q).symm.trans hzero)
  · intro y hzero
    exact hs (Set.inclusion hTW y)
      ((holomorphicGerm_restrict I M hTW y s).symm.trans hzero)
  · intro y
    exact (ha (Set.inclusion hTV y)).trans (fraction_restrict I M hTV p q y).symm
  · intro y
    exact (hb (Set.inclusion hTW y)).trans (fraction_restrict I M hTW r s y).symm

/-- Equality of actual meromorphic germs has a locally constant truth
value. This is derived from local fractions and the analytic identity
principle, not imposed as a property of meromorphic functions. -/
theorem section_equality_eventually_iff {U : Opens M} (a b : Section I M U) (x : U) :
    ∀ᶠ y in 𝓝 x, (a y = b y ↔ a x = b x) := by
  obtain ⟨V, hVU, hxV, p, q, r, s, hq, hs, ha, hb⟩ :=
    common_local_representation I M a b x
  let v : V := ⟨x.val, hxV⟩
  have hcl := isClopen_fraction_eq I M V p q r s hq hs
  have hlocal : ∀ᶠ y in 𝓝 v,
      (fraction I M V p q y = fraction I M V r s y ↔
        fraction I M V p q v = fraction I M V r s v) := by
    by_cases hv : fraction I M V p q v = fraction I M V r s v
    · filter_upwards [hcl.isOpen.mem_nhds hv] with y hy
      exact iff_of_true hy hv
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hv] with y hy
      exact iff_of_false hy hv
  have he : ∀ᶠ y in 𝓝 v, (a (Set.inclusion hVU y) = b (Set.inclusion hVU y) ↔
      a x = b x) := by
    filter_upwards [hlocal] with y hy
    have hav : a x = fraction I M V p q v := ha v
    have hbv : b x = fraction I M V r s v := hb v
    rwa [ha y, hb y, hav, hbv]
  change ∀ᶠ y in Filter.map (Set.inclusion hVU) (𝓝 v), (a y = b y ↔ a x = b x) at he
  have hmap := (Opens.isOpenEmbedding_of_le hVU).map_nhds_eq v
  rw [hmap] at he
  exact he

/-- The equality locus is clopen for arbitrary genuine meromorphic sections. -/
theorem isClopen_section_eq {U : Opens M} (a b : Section I M U) :
    IsClopen {x : U | a x = b x} := by
  refine ⟨?_, ?_⟩
  · apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact (section_equality_eventually_iff I M a b x).mono fun y hy =>
      (not_congr hy).mpr hx
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact (section_equality_eventually_iff I M a b x).mono fun y hy => hy.mpr hx

/-- On a connected original domain, one actual meromorphic germ
determines the entire meromorphic function. -/
theorem section_eq_of_germ_eq {U : Opens M} [PreconnectedSpace U]
    (a b : Section I M U) (x : U) (h : a x = b x) : a = b := by
  have he := (isClopen_section_eq I M a b).eq_univ ⟨x, h⟩
  apply section_ext
  intro y
  have hy : y ∈ ({z : U | a z = b z} : Set U) := by rw [he]; trivial
  exact hy

end Wikipedia.HopfProblem.HolomorphicMeromorphic
