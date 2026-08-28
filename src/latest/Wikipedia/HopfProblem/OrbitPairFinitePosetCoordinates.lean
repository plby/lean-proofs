import Wikipedia.HopfProblem.OrbitPairSubdivisionDimension

/-!
# Faithful coordinates on the native realization of a finite-poset nerve

The vertex-coordinate map is injective: positive nondegenerate
representatives have the same vertex support, hence the same ordered
simplex and the same weights. Compactness makes this a closed embedding.
This supplies an actual geometric model for iterating face-poset nerves.
-/

noncomputable section

universe u

open CategoryTheory Simplicial Topology
open scoped Classical

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex AffineCoordinates Subdivision

variable (P : Type u) [PartialOrder P] [Fintype P]

def coordinates : C(SSet.toTop.obj (nerve P), stdSimplex ℝ P) := by
  classical
  exact nerveInterpolation P (fun p ↦ stdSimplex.vertex p)

theorem coordinates_characteristic (n : ℕ) (x : (nerve P) _⦋n⦌) (t : Simplex n) :
    coordinates P (characteristic (nerve P) n x t) = stdSimplex.map x.obj t := by
  classical
  exact (nerveInterpolation_characteristic P (fun p ↦ stdSimplex.vertex p) n x t).trans
    ((weighted_map x.obj (fun p ↦ stdSimplex.vertex p) t).symm.trans
      (weighted_vertices (stdSimplex.map x.obj t)))

theorem coordinates_vertex (p : P) :
    coordinates P (vertex (nerve P) (ComposableArrows.mk₀ p)) = stdSimplex.vertex p := by
  classical
  exact nerveInterpolation_vertex P (fun p ↦ stdSimplex.vertex p) p

theorem coordinates_injective : Function.Injective (coordinates P) := by
  intro z w hzw
  obtain ⟨n, x, t, ht, rfl⟩ := exists_positive_nonDegenerate (nerve P) z
  obtain ⟨m, y, s, hs, rfl⟩ := exists_positive_nonDegenerate (nerve P) w
  have hx := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono x.val).mp x.property
  have hy := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono y.val).mp y.property
  have hmap : stdSimplex.map x.val.obj t = stdSimplex.map y.val.obj s :=
    (coordinates_characteristic P n x.val t).symm.trans
      (hzw.trans (coordinates_characteristic P m y.val s))
  have hr : Set.range x.val.obj = Set.range y.val.obj := by
    have h := congrArg (fun a : stdSimplex ℝ P ↦ {p | 0 < a p}) hmap
    simpa only [SimplexSupport.positive_support_map x.val.obj t ht,
      SimplexSupport.positive_support_map y.val.obj s hs] using h
  have hnm := congrArg Set.ncard hr
  rw [Set.ncard_range_of_injective hx.injective,
    Set.ncard_range_of_injective hy.injective] at hnm
  have he : n = m := by simpa using hnm
  subst m
  have hobj : x.val.obj = y.val.obj := (hx.range_inj hy).mp hr
  have hxy : x.val = y.val := nerve.ext_of_isThin hobj
  have ht' : t = s := SimplexSupport.map_injective x.val.obj hx.injective
    (hmap.trans (congrArg (fun f : Fin (n + 1) → P ↦ stdSimplex.map f s) hobj.symm))
  exact congrArg₂ (fun (a : (nerve P) _⦋n⦌) (b : Simplex n) ↦
    characteristic (nerve P) n a b) hxy ht'

theorem coordinates_isClosedEmbedding : IsClosedEmbedding (coordinates P) :=
  (coordinates P).continuous.isClosedEmbedding (coordinates_injective P)

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
