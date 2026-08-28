import Wikipedia.NoExoticSixSphere.JamesSphereConeQuotient
import Wikipedia.NoExoticSixSphere.ContractedQuotientNativeHomotopy

/-!
# The actual cone collapse on native homotopy groups

Contract the attached disk linearly to any chosen point of its image,
fixing that point. Homotopy extension retains this fixed point in the
whole cone model. The original collapse consequently induces bijections
on native homotopy classes at every point of the cone image.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

def diskContraction (n : ℕ) (a : CompactCellAttachment.Disk (ConeCoordinates n)) :
    (ContinuousMap.id (CompactCellAttachment.Disk (ConeCoordinates n))).HomotopyRel
      (ContinuousMap.const _ a) {a} where
  toFun z := ⟨(1 - (z.1 : ℝ)) • z.2.val + (z.1 : ℝ) • a.val,
    (convex_closedBall (0 : ConeCoordinates n) 1) z.2.property a.property
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  map_zero_left z := by
    apply Subtype.ext
    simp
  map_one_left z := by
    apply Subtype.ext
    simp
  prop' t z hz := by
    have he : z = a := hz
    subst z
    apply Subtype.ext
    change (1 - (t : ℝ)) • a.val + (t : ℝ) • a.val = a.val
    rw [← add_smul, sub_add_cancel, one_smul]

theorem exists_extended_contraction_at (n : ℕ) (a : Set.range (cone n)) :
    ∃ g : C(Space n, Space n), ∃ H : (ContinuousMap.id (Space n)).HomotopyRel g {a.val},
      (∀ x ∈ Set.range (cone n), g x = a.val) ∧
      ∀ t x, x ∈ Set.range (cone n) → H (t, x) ∈ Set.range (cone n) := by
  let e := (cone_isClosedEmbedding n).isEmbedding.toHomeomorph
  let d := e.symm a
  have hd : cone n d = a.val := congrArg Subtype.val (e.apply_symm_apply a)
  let K := diskContraction n d
  let G := (cone n).comp K.toContinuousMap
  have hG : ∀ z, G (0, z) = (ContinuousMap.id (Space n)) (cone n z) := by
    intro z
    change cone n (K (0, z)) = cone n z
    exact congrArg (cone n) (K.map_zero_left z)
  obtain ⟨L, hL0, hLC⟩ := cone_hasHomotopyExtension n (TopCat.of (Space n))
    (ContinuousMap.id (Space n)) G hG
  have hLC' : ∀ t z, L (t, cone n z) = G (t, z) := hLC
  let g : C(Space n, Space n) := ⟨fun x ↦ L (1, x),
    L.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H : (ContinuousMap.id (Space n)).HomotopyRel g {a.val} := {
    toContinuousMap := L
    map_zero_left := hL0
    map_one_left _ := rfl
    prop' := by
      rintro t x (rfl : x = a.val)
      change L (t, a.val) = a.val
      rw [← hd, hLC']
      change cone n (K (t, d)) = cone n d
      rw [K.eq_fst t (Set.mem_singleton d)]
      rfl }
  refine ⟨g, H, ?_, ?_⟩
  · rintro x ⟨z, rfl⟩
    change L (1, cone n z) = a.val
    rw [hLC']
    change cone n (K (1, z)) = a.val
    exact (congrArg (cone n) (K.map_one_left z)).trans hd
  · rintro t x ⟨z, rfl⟩
    change L (t, cone n z) ∈ Set.range (cone n)
    rw [hLC']
    exact Set.mem_range_self (K (t, z))

theorem collapse_map_bijective (n : ℕ) (a : Set.range (cone n)) (N : Type*) :
    Function.Bijective (HigherHomotopy.map (N := N) (collapse n) (y := a.val) rfl) := by
  let : T2Space (SecondStage.QuotientSpace n) := (SecondStage.quotientHomeomorph n).symm.t2Space
  obtain ⟨g, H, hg, hH⟩ := exists_extended_contraction_at n a
  exact ContractedQuotient.map_bijective_of_fixed_contraction (collapse n)
    (collapse_isQuotientMap n) (Set.range (cone n)) (collapse_eq_iff n) a.val a.property hg H hH

end NoExoticSixSphere.JamesSphere.SecondStageCone
