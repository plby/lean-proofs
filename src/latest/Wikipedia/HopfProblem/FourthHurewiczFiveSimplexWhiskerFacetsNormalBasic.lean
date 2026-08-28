import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerBased

/-!
# Normal whisker facets: literal coordinates and based outer arms

On a normal facet, either an unchanged coordinate is an endpoint or the
last coordinate is zero. Together with an endpoint of the first coordinate,
this places both outer arms on the actual codimension-two boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

/-- Facet insertion commutes with prepending the independent path coordinate. -/
theorem cubeFacet_succ_cons (n : ℕ) (i : Fin (n + 1)) (ε s : I)
    (u : Fin n → I) :
    cubeFacet (n + 1) i.succ ε (Fin.cons s u) =
      Fin.cons s (cubeFacet n i ε u) :=
  Fin.insertNth_succ_cons i ε s u

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- The literal normal-facet outer arm is based at every radius. -/
theorem whiskerFacetNormal_arm_based (F : BasedCubicalCell (n + 2) x)
    (i : Fin (n + 1)) (ε : I) (hε : ε = 0 ∨ ε = 1)
    (h : i ≠ Fin.last n ∨ ε = 0) (u : Fin n → I)
    (a : I) (ha : a = 0 ∨ a = 1) (r : I) :
    F.val (Fin.cons a (Fin.snoc (Fin.init (cubeFacet n i ε u))
      (r * cubeFacet n i ε u (Fin.last n)))) = x := by
  cases i using Fin.lastCases with
  | last =>
    have hzero : ε = 0 := h.resolve_left (not_not_intro rfl)
    subst ε
    apply F.property _ 0 (Fin.last n).succ (by simp)
    · simpa only [Fin.cons_zero] using ha
    · exact Or.inl (by simp)
  | cast i =>
    apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
    · simpa only [Fin.cons_zero] using ha
    · simpa [Fin.init] using hε

/-- On the middle rectangle edge, the original facet has exactly its original
ordered coordinates, with the independent path coordinate prepended. -/
theorem cubicalFace_succ_cons (F : BasedCubicalCell (n + 2) x)
    (i : Fin (n + 1)) (ε : I) (hε : ε = 0 ∨ ε = 1)
    (u : Fin n → I) (s : I) :
    cubicalFace F i.succ ε hε (Fin.cons s u) =
      F.val (Fin.cons s (cubeFacet n i ε u)) := by
  rw [cubicalFace_apply, cubeFacet_succ_cons]

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
