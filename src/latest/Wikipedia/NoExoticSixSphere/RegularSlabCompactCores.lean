import Wikipedia.NoExoticSixSphere.RegularSlabInteriorEquivalence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sets.Compacts

/-!
# Cofinal actual compact cores of a collared regular slab

Every compact subset of the strict-time interior lies strictly between
two inner times whose exterior intervals are still constant collars.
The corresponding bounded fiber is an actual compact subset of the
original interior. These cores are cofinal among compact supports, as
needed to compare compact-support cohomology with a boundary-relative
cohomology group.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)

def interiorTime : C(CylinderFiberSlab.interiorDomain d.map z s t, ℝ) where
  toFun p := p.val.val.val.1
  continuous_toFun := continuous_fst.comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))

theorem exists_inner_times_around_compact
    (K : Compacts (CylinderFiberSlab.interiorDomain d.map z s t)) :
    ∃ a b : ℝ, s < a ∧ a ≤ b ∧ b < t ∧
      Icc s a ⊆ d.leftTimes ∧ Icc b t ⊆ d.rightTimes ∧
      ∀ p ∈ K, a < d.interiorTime p ∧ d.interiorTime p < b := by
  obtain ⟨a₀, b₀, hsa, hab, hbt, hL, hR⟩ := d.exists_inner_times
  by_cases hne : (K : Set (CylinderFiberSlab.interiorDomain d.map z s t)).Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := K.isCompact.exists_isMinOn hne d.interiorTime.continuous.continuousOn
    obtain ⟨p₁, hp₁, hmax⟩ := K.isCompact.exists_isMaxOn hne d.interiorTime.continuous.continuousOn
    let a := min a₀ ((s + d.interiorTime p₀) / 2)
    let b := max b₀ ((d.interiorTime p₁ + t) / 2)
    have ha₀ : a ≤ a₀ := min_le_left _ _
    have hb₀ : b₀ ≤ b := le_max_left _ _
    have hsa' : s < a := lt_min hsa (by
      have hp : s < d.interiorTime p₀ := p₀.property.1
      linarith)
    have hbt' : b < t := max_lt hbt (by
      have hp : d.interiorTime p₁ < t := p₁.property.2
      linarith)
    refine ⟨a, b, hsa', ha₀.trans (hab.trans hb₀), hbt',
      (Icc_subset_Icc le_rfl ha₀).trans hL, (Icc_subset_Icc hb₀ le_rfl).trans hR, ?_⟩
    intro p hp
    have hamin : a ≤ (s + d.interiorTime p₀) / 2 := min_le_right _ _
    have hbmax : (d.interiorTime p₁ + t) / 2 ≤ b := le_max_right _ _
    have hlo : d.interiorTime p₀ ≤ d.interiorTime p := hmin hp
    have hhi : d.interiorTime p ≤ d.interiorTime p₁ := hmax hp
    have hp₀' : s < d.interiorTime p₀ := p₀.property.1
    have hp₁' : d.interiorTime p₁ < t := p₁.property.2
    exact ⟨by linarith, by linarith⟩
  · exact ⟨a₀, b₀, hsa, hab, hbt, hL, hR, fun p hp ↦ (hne ⟨p, hp⟩).elim⟩

def coreInclusion (a b : ℝ) (hsa : s < a) (hbt : b < t) :
    C(CylinderFiberSlab.slab d.map z a b, CylinderFiberSlab.interiorDomain d.map z s t) where
  toFun p := ⟨⟨p.val, ⟨hsa.le.trans p.property.1, p.property.2.trans hbt.le⟩⟩,
    ⟨hsa.trans_le p.property.1, p.property.2.trans_lt hbt⟩⟩
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [CompactSpace M] [T2Space N]

def compactCore (a b : ℝ) (hsa : s < a) (hbt : b < t) :
    Compacts (CylinderFiberSlab.interiorDomain d.map z s t) :=
  letI := CylinderFiberSlab.compactSpace d.map z a b
  ⟨range (d.coreInclusion a b hsa hbt), isCompact_range (d.coreInclusion a b hsa hbt).continuous⟩

theorem mem_compactCore_iff (a b : ℝ) (hsa : s < a) (hbt : b < t)
    (p : CylinderFiberSlab.interiorDomain d.map z s t) :
    p ∈ d.compactCore a b hsa hbt ↔ d.interiorTime p ∈ Icc a b := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p.val.val, hp⟩, rfl⟩

theorem compactCore_cofinal (K : Compacts (CylinderFiberSlab.interiorDomain d.map z s t)) :
    ∃ (a b : ℝ) (hsa : s < a) (hbt : b < t), a ≤ b ∧
      Icc s a ⊆ d.leftTimes ∧ Icc b t ⊆ d.rightTimes ∧ K ≤ d.compactCore a b hsa hbt := by
  obtain ⟨a, b, hsa, hab, hbt, hL, hR, hK⟩ := d.exists_inner_times_around_compact K
  refine ⟨a, b, hsa, hbt, hab, hL, hR, ?_⟩
  intro p hp
  exact (d.mem_compactCore_iff a b hsa hbt p).mpr ⟨(hK p hp).1.le, (hK p hp).2.le⟩

end NoExoticSixSphere.RegularCollaredCylinder
