import Wikipedia.NoExoticSixSphere.SphereCylinderPoles
import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative
import Wikipedia.NoExoticSixSphere.UnorderedSphereDoublePoints

/-!
# The actual Whitney three-sphere map

In head-tail coordinates the map is `(t,u) ↦ (u,t • u)` on the unit
three-sphere. Its only distinct coincident source points are the two poles.
All maps use the original sphere atlas and ordinary vector coordinates.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.WhitneySphere

open GLOrthonormalization SphereCylinder

def head : Vector 4 →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Vector 3)).comp (join 2).symm.toContinuousLinearMap

theorem head_apply (v : Vector 4) : head v = v 0 := rfl

theorem join_head_tail (v : Vector 4) : join 2 (head v, tail 2 v) = v :=
  (join 2).apply_symm_apply v

def ambientMap (v : Vector 4) : Vector 3 × Vector 3 := (tail 2 v, head v • tail 2 v)

theorem contDiff_ambientMap : ContDiff ℝ ∞ ambientMap :=
  (tail 2).contDiff.prodMk (head.contDiff.smul (tail 2).contDiff)

def map (x : Sphere 3) : Vector 3 × Vector 3 := ambientMap x.val

theorem contMDiff_map : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ map := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact contDiff_ambientMap.contMDiff.comp contMDiff_coe_sphere

def continuousMap : C(Sphere 3, Vector 3 × Vector 3) := ⟨map, contMDiff_map.continuous⟩

theorem map_endPole (b : Bool) : map (endPole 2 b) = 0 := by
  simp only [map, ambientMap, tail_endPole, smul_zero]
  rfl

theorem map_eq_of_tail_ne_zero {x y : Sphere 3} (hx : tail 2 x.val ≠ 0)
    (h : map x = map y) : x = y := by
  have ht : tail 2 x.val = tail 2 y.val := congrArg Prod.fst h
  have hs : head x.val • tail 2 x.val = head y.val • tail 2 y.val := congrArg Prod.snd h
  rw [← ht] at hs
  have hh : head x.val = head y.val := smul_left_injective ℝ hx hs
  apply Subtype.ext
  rw [← join_head_tail x.val, ← join_head_tail y.val, hh, ht]

theorem distinct_coincidence_iff (x y : Sphere 3) :
    x ≠ y ∧ map x = map y ↔
      (x = endPole 2 false ∧ y = endPole 2 true) ∨
      (x = endPole 2 true ∧ y = endPole 2 false) := by
  constructor
  · rintro ⟨hne, he⟩
    have hx : x ∉ band 2 := fun hx ↦ hne (map_eq_of_tail_ne_zero hx he)
    have hy : y ∉ band 2 := fun hy ↦ hne (map_eq_of_tail_ne_zero hy he.symm).symm
    rcases (not_mem_band_iff 2 x).mp hx with rfl | rfl <;>
      rcases (not_mem_band_iff 2 y).mp hy with rfl | rfl
    · exact (hne rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (hne rfl).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨endPoles_ne 2, (map_endPole false).trans (map_endPole true).symm⟩
    · exact ⟨(endPoles_ne 2).symm, (map_endPole true).trans (map_endPole false).symm⟩

def orderedPair (b : Bool) : SphereSelfIntersections.pairs map :=
  if b then ⟨(endPole 2 true, endPole 2 false),
    (distinct_coincidence_iff _ _).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  else ⟨(endPole 2 false, endPole 2 true),
    (distinct_coincidence_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩

theorem orderedPair_bijective : Bijective orderedPair := by
  constructor
  · intro b c h
    cases b <;> cases c
    · rfl
    · exact ((endPoles_ne 2)
        (congrArg (fun p : SphereSelfIntersections.pairs map ↦ p.val.1) h)).elim
    · exact ((endPoles_ne 2)
        (congrArg (fun p : SphereSelfIntersections.pairs map ↦ p.val.1) h).symm).elim
    · rfl
  · intro p
    rcases (distinct_coincidence_iff p.val.1 p.val.2).mp p.property with h | h
    · exact ⟨false, Subtype.ext (Prod.ext h.1.symm h.2.symm)⟩
    · exact ⟨true, Subtype.ext (Prod.ext h.1.symm h.2.symm)⟩

def orderedPairEquiv : Bool ≃ SphereSelfIntersections.pairs map :=
  Equiv.ofBijective orderedPair orderedPair_bijective

theorem finite_pairs : (SphereSelfIntersections.pairs map).Finite :=
  finite_coe_iff.mp (Finite.of_equiv Bool orderedPairEquiv)

theorem ordered_ncard : (SphereSelfIntersections.pairs map).ncard = 2 := by
  change Nat.card (SphereSelfIntersections.pairs map) = 2
  rw [← Nat.card_congr orderedPairEquiv]
  simp

theorem unordered_ncard : Nat.card (SphereSelfIntersections.Unordered map) = 1 := by
  have h := SphereSelfIntersections.ordered_ncard_eq_twice_unordered map finite_pairs
  rw [ordered_ncard] at h
  omega

theorem unorderedParity_one : SphereSelfIntersections.unorderedParity map = 1 := by
  simp only [SphereSelfIntersections.unorderedParity, unordered_ncard, Nat.cast_one]

end NoExoticSixSphere.WhitneySphere
