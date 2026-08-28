import Wikipedia.HopfProblem.CuspHoneycombHexagonArcs

/-!
# Gluing six parametrizations of the actual boundary cycle

Six homeomorphisms onto the actual component intersections, with the same
endpoints as the standard arcs, give a homeomorphism of their literal union.
Continuity uses the compact finite-arc quotient topology, and the exact
fibres follow from the proved toric triple-point intersection pattern.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

/-- Inclusion of one actual component intersection into their boundary union. -/
def boundaryArcInclusion (k : Fin 6) (x : positiveBoundary k) :
    (⋃ j : Fin 6, positiveBoundary j) :=
  ⟨x.1, Set.mem_iUnion.mpr ⟨k, x.2⟩⟩

@[simp] theorem boundaryArcInclusion_coe (k : Fin 6) (x : positiveBoundary k) :
    (boundaryArcInclusion k x : PositiveE0) = x.1 := rfl

theorem boundaryArcInclusion_continuous (k : Fin 6) :
    Continuous (boundaryArcInclusion k) := continuous_subtype_val.subtype_mk _

/-- Six compact intervals mapped onto the literal actual boundary cycle. -/
def boundaryArcProjection (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (p : Fin 6 × unitInterval) : (⋃ j : Fin 6, positiveBoundary j) :=
  boundaryArcInclusion p.1 (P p.1 p.2)

theorem boundaryArcProjection_continuous
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) :
    Continuous (boundaryArcProjection P) :=
  continuous_prod_of_discrete_left.mpr (fun k =>
    (boundaryArcInclusion_continuous k).comp (P k).continuous)

theorem boundaryArcProjection_surjective
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) :
    Function.Surjective (boundaryArcProjection P) := by
  intro x
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp x.2
  obtain ⟨t, ht⟩ := (P k).surjective ⟨x.1, hk⟩
  refine ⟨(k, t), ?_⟩
  apply Subtype.ext
  change (P k t).1 = x.1
  exact congrArg (fun y : positiveBoundary k => y.1) ht

/-- This is the original boundary subspace topology, not a substituted
topology on an abstract six-cycle. -/
theorem boundaryArcProjection_isQuotientMap
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) :
    IsQuotientMap (boundaryArcProjection P) :=
  (boundaryArcProjection_continuous P).isClosedMap.isQuotientMap
    (boundaryArcProjection_continuous P) (boundaryArcProjection_surjective P)

theorem boundaryArcFamily_eq_self_iff
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (i : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P i u).1 ↔ t = u := by
  constructor
  · intro h
    exact (P i).injective (Subtype.ext h)
  · rintro rfl
    rfl

theorem boundaryArcFamily_eq_next_iff
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)
    (i : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P (i + 1) u).1 ↔ t = 1 ∧ u = 0 := by
  constructor
  · intro h
    have hm : (P i t).1 ∈ positiveBoundary i ∩ positiveBoundary (i + 1) := by
      refine ⟨(P i t).2, ?_⟩
      rw [h]
      exact (P (i + 1) u).2
    have hx : (P i t).1 = squarePoint i cornerZero := by
      simpa only [positiveBoundary_inter_next, Set.mem_singleton_iff] using hm
    constructor
    · apply (P i).injective
      apply Subtype.ext
      rw [hP1 i, positiveBoundaryArc_one]
      exact hx
    · apply (P (i + 1)).injective
      apply Subtype.ext
      rw [hP0 (i + 1), positiveBoundaryArc_zero, add_sub_cancel_right]
      exact h.symm.trans hx
  · rintro ⟨rfl, rfl⟩
    rw [hP1 i, hP0 (i + 1)]
    exact positiveBoundaryArc_next_endpoint i

theorem boundaryArcFamily_ne_nonadjacent
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    {i j : Fin 6} (hij : i ≠ j) (hnext : j ≠ i + 1) (hprev : i ≠ j + 1)
    (t u : unitInterval) : (P i t).1 ≠ (P j u).1 := by
  intro h
  apply Set.disjoint_left.mp (positiveBoundary_disjoint_nonadjacent hij hnext hprev)
    (P i t).2
  rw [h]
  exact (P j u).2

/-- Any two endpoint-compatible families identify precisely the same
points of the six intervals. -/
theorem boundaryArcFamilies_sameFibres
    (P Q : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)
    (hQ0 : ∀ k, (Q k 0).1 = (positiveBoundaryArc k 0).1)
    (hQ1 : ∀ k, (Q k 1).1 = (positiveBoundaryArc k 1).1)
    (i j : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P j u).1 ↔ (Q i t).1 = (Q j u).1 := by
  by_cases hij : i = j
  · subst j
    rw [boundaryArcFamily_eq_self_iff, boundaryArcFamily_eq_self_iff]
  by_cases hnext : j = i + 1
  · subst j
    rw [boundaryArcFamily_eq_next_iff P hP0 hP1,
      boundaryArcFamily_eq_next_iff Q hQ0 hQ1]
  by_cases hprev : i = j + 1
  · subst i
    rw [eq_comm (a := (P (j + 1) t).1), eq_comm (a := (Q (j + 1) t).1),
      boundaryArcFamily_eq_next_iff P hP0 hP1,
      boundaryArcFamily_eq_next_iff Q hQ0 hQ1]
  exact iff_of_false (boundaryArcFamily_ne_nonadjacent P hij hnext hprev t u)
    (boundaryArcFamily_ne_nonadjacent Q hij hnext hprev t u)

theorem boundaryArcProjection_sameFibres
    (P Q : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)
    (hQ0 : ∀ k, (Q k 0).1 = (positiveBoundaryArc k 0).1)
    (hQ1 : ∀ k, (Q k 1).1 = (positiveBoundaryArc k 1).1)
    (a b : Fin 6 × unitInterval) :
    boundaryArcProjection P a = boundaryArcProjection P b ↔
      boundaryArcProjection Q a = boundaryArcProjection Q b := by
  have h := boundaryArcFamilies_sameFibres P Q hP0 hP1 hQ0 hQ1 a.1 b.1 a.2 b.2
  constructor
  · intro hab
    apply Subtype.ext
    exact h.mp (congrArg Subtype.val hab)
  · intro hab
    apply Subtype.ext
    exact h.mpr (congrArg Subtype.val hab)

variable (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)

/-- Gluing the six prescribed actual arc homeomorphisms gives a genuine
homeomorphism of the actual boundary union. -/
def boundaryGluingHomeomorph :
    (⋃ k : Fin 6, positiveBoundary k) ≃ₜ (⋃ k : Fin 6, positiveBoundary k) :=
  CommonFibres.homeomorph (boundaryArcProjection positiveBoundaryArc)
    (boundaryArcProjection P) (boundaryArcProjection_surjective positiveBoundaryArc)
    (boundaryArcProjection_continuous positiveBoundaryArc)
    (boundaryArcProjection_continuous P) (boundaryArcProjection_surjective P)
    (boundaryArcProjection_sameFibres positiveBoundaryArc P
      (fun _ => rfl) (fun _ => rfl) hP0 hP1)

/-- The glued map agrees exactly with the prescribed map on each arc,
including both shared endpoints. -/
@[simp] theorem boundaryGluingHomeomorph_apply (k : Fin 6) (t : unitInterval) :
    boundaryGluingHomeomorph P hP0 hP1
      (boundaryArcInclusion k (positiveBoundaryArc k t)) = boundaryArcInclusion k (P k t) :=
  CommonFibres.homeomorph_apply (boundaryArcProjection positiveBoundaryArc)
    (boundaryArcProjection P) (boundaryArcProjection_surjective positiveBoundaryArc)
    (boundaryArcProjection_continuous positiveBoundaryArc)
    (boundaryArcProjection_continuous P) (boundaryArcProjection_surjective P)
    (boundaryArcProjection_sameFibres positiveBoundaryArc P
      (fun _ => rfl) (fun _ => rfl) hP0 hP1) (k, t)

@[simp] theorem boundaryGluingHomeomorph_coe (k : Fin 6) (t : unitInterval) :
    (boundaryGluingHomeomorph P hP0 hP1
      (boundaryArcInclusion k (positiveBoundaryArc k t)) : PositiveE0) = (P k t).1 :=
  congrArg Subtype.val (boundaryGluingHomeomorph_apply P hP0 hP1 k t)

@[simp] theorem boundaryGluingHomeomorph_symm_apply (k : Fin 6) (t : unitInterval) :
    (boundaryGluingHomeomorph P hP0 hP1).symm (boundaryArcInclusion k (P k t)) =
      boundaryArcInclusion k (positiveBoundaryArc k t) := by
  apply (boundaryGluingHomeomorph P hP0 hP1).injective
  rw [Homeomorph.apply_symm_apply, boundaryGluingHomeomorph_apply]

@[simp] theorem boundaryGluingHomeomorph_symm_coe (k : Fin 6) (t : unitInterval) :
    ((boundaryGluingHomeomorph P hP0 hP1).symm
      (boundaryArcInclusion k (P k t)) : PositiveE0) = (positiveBoundaryArc k t).1 :=
  congrArg Subtype.val (boundaryGluingHomeomorph_symm_apply P hP0 hP1 k t)

/-- The glued homeomorphism preserves each literal component intersection,
and therefore also preserves all their vertex intersections. -/
theorem boundaryGluingHomeomorph_mem_boundary_iff
    (x : (⋃ j : Fin 6, positiveBoundary j)) (k : Fin 6) :
    (boundaryGluingHomeomorph P hP0 hP1 x : PositiveE0) ∈ positiveBoundary k ↔
      (x : PositiveE0) ∈ positiveBoundary k := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := (P k).surjective
      ⟨(boundaryGluingHomeomorph P hP0 hP1 x : PositiveE0), hx⟩
    have hy : boundaryArcInclusion k (P k t) = boundaryGluingHomeomorph P hP0 hP1 x := by
      apply Subtype.ext
      exact congrArg (fun y : positiveBoundary k => y.1) ht
    have he : x = (boundaryGluingHomeomorph P hP0 hP1).symm
        (boundaryArcInclusion k (P k t)) := by
      apply (boundaryGluingHomeomorph P hP0 hP1).injective
      rw [Homeomorph.apply_symm_apply, hy]
    rw [he, boundaryGluingHomeomorph_symm_coe]
    exact (positiveBoundaryArc k t).2
  · intro hx
    obtain ⟨t, ht⟩ := (positiveBoundaryArc k).surjective ⟨x.1, hx⟩
    have he : boundaryArcInclusion k (positiveBoundaryArc k t) = x := by
      apply Subtype.ext
      exact congrArg (fun y : positiveBoundary k => y.1) ht
    rw [← he, boundaryGluingHomeomorph_coe]
    exact (P k t).2

end Wikipedia.HopfProblem.CuspHoneycombHexagon
