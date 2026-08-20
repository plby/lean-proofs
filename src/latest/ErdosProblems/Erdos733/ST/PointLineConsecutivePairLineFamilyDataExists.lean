import ErdosProblems.Erdos733.ST.PointLineConsecutivePairLineFamilyData
import ErdosProblems.Erdos733.ST.FiniteRealAdjacentPairsExists

open Classical
noncomputable section

-- [TABLET NODE: PointLineConsecutivePairLineFamilyDataExists]
lemma PointLineConsecutivePairLineFamilyDataExists
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
      IsAffineLine ell}) :
    Nonempty (PointLineConsecutivePairLineFamilyData P L) := by
-- BODY
  let retained := L.filter fun ell ↦
    ∃ p : P, (p.1 : EuclideanSpace ℝ (Fin 2)) ∈ ell.1
  let coordEquiv (ell : retained) : ℝ ≃ₗ[ℝ] ell.1.1.direction :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one ell.1.2.2).some
  let coord (ell : retained) : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x ↦ (coordEquiv ell).symm (ell.1.1.direction.orthogonalProjection x)
  have coord_inj : ∀ (ell : retained) {x y},
      x ∈ ell.1.1 → y ∈ ell.1.1 → coord ell x = coord ell y → x = y := by
    intro ell x y hx hy hxy
    have hsub : x - y ∈ ell.1.1.direction :=
      AffineSubspace.vsub_mem_direction hx hy
    have hproj : ell.1.1.direction.orthogonalProjection (x - y) =
        (⟨x - y, hsub⟩ : ell.1.1.direction) := by
      simpa using ell.1.1.direction.orthogonalProjection_mem_subspace_eq_self
        (⟨x - y, hsub⟩ : ell.1.1.direction)
    have hcsub : coord ell (x - y) = 0 := by
      dsimp [coord] at hxy ⊢
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr hxy
    have hsubzero : x - y = 0 := by
      have hz : (coordEquiv ell).symm
          (⟨x - y, hsub⟩ : ell.1.1.direction) = 0 := by
        rw [← hproj]
        exact hcsub
      have hz' : (⟨x - y, hsub⟩ : ell.1.1.direction) = 0 :=
        (coordEquiv ell).symm.injective
          (hz.trans (map_zero (coordEquiv ell).symm).symm)
      exact congrArg Subtype.val hz'
    exact sub_eq_zero.mp hsubzero
  have coord_affine : ∀ (ell : retained) {x y},
      x ∈ ell.1.1 → y ∈ ell.1.1 → ∀ t : ℝ,
      coord ell ((1 - t) • x + t • y) =
        (1 - t) * coord ell x + t * coord ell y := by
    intro ell x y hx hy t
    dsimp [coord]
    simp only [map_add, map_smul, smul_eq_mul]
  let fiberFinset (ell : retained) : Finset (EuclideanSpace ℝ (Fin 2)) :=
    P.filter fun p ↦ p ∈ ell.1.1
  let Fiber (ell : retained) := ↥(fiberFinset ell)
  have fiber_nonempty (ell : retained) : Nonempty (Fiber ell) := by
    have hex := (Finset.mem_filter.mp ell.2).2
    rcases hex with ⟨p, hp⟩
    exact ⟨⟨p.1, Finset.mem_filter.mpr ⟨p.2, hp⟩⟩⟩
  have edge_exists (ell : retained) :
      ∃ E : Finset (Fiber ell × Fiber ell),
        (∀ p q, (p, q) ∈ E ↔
          p ∈ (Finset.univ : Finset (Fiber ell)) ∧
          q ∈ (Finset.univ : Finset (Fiber ell)) ∧
          coord ell p.1 < coord ell q.1 ∧
          ∀ r ∈ (Finset.univ : Finset (Fiber ell)),
            ¬(coord ell p.1 < coord ell r.1 ∧
              coord ell r.1 < coord ell q.1)) ∧
        (∀ e1 e2, e1 ∈ E → e2 ∈ E → e1 ≠ e2 →
          Disjoint (Set.Ioo (coord ell e1.1.1) (coord ell e1.2.1))
            (Set.Ioo (coord ell e2.1.1) (coord ell e2.2.1))) ∧
        (∀ e1 e2, e1 ∈ E → e2 ∈ E → e1 ≠ e2 →
          (Set.Icc (coord ell e1.1.1) (coord ell e1.2.1) ∩
            Set.Icc (coord ell e2.1.1) (coord ell e2.2.1)).Subsingleton) ∧
        E.card + 1 = (Finset.univ : Finset (Fiber ell)).card := by
    apply FiniteRealAdjacentPairsExists
    · intro p q hpq
      apply Subtype.ext
      exact coord_inj ell
        (Finset.mem_filter.mp p.2).2 (Finset.mem_filter.mp q.2).2 hpq
    · rcases fiber_nonempty ell with ⟨p⟩
      exact ⟨p, Finset.mem_univ p⟩
  let rawEdges (ell : retained) : Finset (Fiber ell × Fiber ell) :=
    (edge_exists ell).choose
  have rawSpec (ell : retained) := (edge_exists ell).choose_spec
  let edgeEmb (ell : retained) : (Fiber ell × Fiber ell) ↪ (P × P) :=
    { toFun := fun e ↦
        (⟨e.1.1, (Finset.mem_filter.mp e.1.2).1⟩,
          ⟨e.2.1, (Finset.mem_filter.mp e.2.2).1⟩)
      inj' := by
        intro e1 e2 h
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun e : P × P ↦ e.1.1) h
        · apply Subtype.ext
          exact congrArg (fun e : P × P ↦ e.2.1) h }
  let chosenEdges (ell : retained) : Finset (P × P) :=
    (rawEdges ell).map (edgeEmb ell)
  have local_mem : ∀ (ell : retained) (p q : P),
      (p, q) ∈ chosenEdges ell ↔
        (p.1 : EuclideanSpace ℝ (Fin 2)) ∈ ell.1.1 ∧
        (q.1 : EuclideanSpace ℝ (Fin 2)) ∈ ell.1.1 ∧
        coord ell p.1 < coord ell q.1 ∧
        ∀ r : P, (r.1 : EuclideanSpace ℝ (Fin 2)) ∈ ell.1.1 →
          ¬(coord ell p.1 < coord ell r.1 ∧ coord ell r.1 < coord ell q.1) := by
    intro ell p q
    constructor
    · intro hpq
      rcases Finset.mem_map.mp hpq with ⟨e, he, heq⟩
      change
        (⟨e.1.1, (Finset.mem_filter.mp e.1.2).1⟩,
          ⟨e.2.1, (Finset.mem_filter.mp e.2.2).1⟩) = (p, q) at heq
      have hp : (⟨e.1.1, (Finset.mem_filter.mp e.1.2).1⟩ : P) = p :=
        congrArg Prod.fst heq
      have hq : (⟨e.2.1, (Finset.mem_filter.mp e.2.2).1⟩ : P) = q :=
        congrArg Prod.snd heq
      subst p
      subst q
      have hs := (rawSpec ell).1 e.1 e.2 |>.mp he
      refine ⟨(Finset.mem_filter.mp e.1.2).2,
        (Finset.mem_filter.mp e.2.2).2, hs.2.2.1, ?_⟩
      intro r hr hbetween
      let rr : Fiber ell := ⟨r.1, Finset.mem_filter.mpr ⟨r.2, hr⟩⟩
      exact hs.2.2.2 rr (Finset.mem_univ rr) hbetween
    · rintro ⟨hp, hq, hpq, hno⟩
      let pp : Fiber ell := ⟨p.1, Finset.mem_filter.mpr ⟨p.2, hp⟩⟩
      let qq : Fiber ell := ⟨q.1, Finset.mem_filter.mpr ⟨q.2, hq⟩⟩
      have he : (pp, qq) ∈ rawEdges ell := (rawSpec ell).1 pp qq |>.mpr ⟨
        Finset.mem_univ pp, Finset.mem_univ qq, hpq, by
          intro r hr hbetween
          exact hno ⟨r.1, (Finset.mem_filter.mp r.2).1⟩
            (Finset.mem_filter.mp r.2).2 hbetween⟩
      exact Finset.mem_map.mpr ⟨(pp, qq), he, rfl⟩
  have local_card : ∀ ell : retained,
      (chosenEdges ell).card + 1 = (fiberFinset ell).card := by
    intro ell
    calc
      (chosenEdges ell).card + 1 = (rawEdges ell).card + 1 := by simp [chosenEdges]
      _ = (Finset.univ : Finset (Fiber ell)).card := (rawSpec ell).2.2.2
      _ = (fiberFinset ell).card := by simp [Fiber]
  have coord_openSegment : ∀ (ell : retained) {x y z},
      x ∈ ell.1.1 → y ∈ ell.1.1 → coord ell x < coord ell y →
      z ∈ openSegment ℝ x y →
      coord ell z ∈ Set.Ioo (coord ell x) (coord ell y) ∧ z ∈ ell.1.1 := by
    intro ell x y z hx hy hxy hz
    rw [openSegment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    constructor
    · rw [AffineMap.lineMap_apply_module, coord_affine ell hx hy t]
      constructor
      · nlinarith [mul_pos ht.1 (sub_pos.mpr hxy)]
      · nlinarith [mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hxy)]
    · exact AffineMap.lineMap_mem t hx hy
  have coord_segment : ∀ (ell : retained) {x y z},
      x ∈ ell.1.1 → y ∈ ell.1.1 → coord ell x < coord ell y →
      z ∈ segment ℝ x y →
      coord ell z ∈ Set.Icc (coord ell x) (coord ell y) ∧ z ∈ ell.1.1 := by
    intro ell x y z hx hy hxy hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    constructor
    · rw [AffineMap.lineMap_apply_module, coord_affine ell hx hy t]
      constructor
      · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hxy.le)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hxy.le)]
    · exact AffineMap.lineMap_mem t hx hy
  have local_open_disjoint : ∀ (ell : retained) (e1 e2 : P × P),
      e1 ∈ chosenEdges ell → e2 ∈ chosenEdges ell → e1 ≠ e2 →
      Disjoint (Set.Ioo (coord ell e1.1.1) (coord ell e1.2.1))
        (Set.Ioo (coord ell e2.1.1) (coord ell e2.2.1)) := by
    intro ell e1 e2 he1 he2 hne
    change e1 ∈ (rawEdges ell).map (edgeEmb ell) at he1
    change e2 ∈ (rawEdges ell).map (edgeEmb ell) at he2
    rcases Finset.mem_map.mp he1 with ⟨f1, hf1, rfl⟩
    rcases Finset.mem_map.mp he2 with ⟨f2, hf2, rfl⟩
    have hfne : f1 ≠ f2 := fun h ↦ hne (congrArg (edgeEmb ell) h)
    convert (rawSpec ell).2.1 f1 f2 hf1 hf2 hfne using 1 <;> rfl
  have local_closed_subsingleton : ∀ (ell : retained) (e1 e2 : P × P),
      e1 ∈ chosenEdges ell → e2 ∈ chosenEdges ell → e1 ≠ e2 →
      (Set.Icc (coord ell e1.1.1) (coord ell e1.2.1) ∩
        Set.Icc (coord ell e2.1.1) (coord ell e2.2.1)).Subsingleton := by
    intro ell e1 e2 he1 he2 hne
    change e1 ∈ (rawEdges ell).map (edgeEmb ell) at he1
    change e2 ∈ (rawEdges ell).map (edgeEmb ell) at he2
    rcases Finset.mem_map.mp he1 with ⟨f1, hf1, rfl⟩
    rcases Finset.mem_map.mp he2 with ⟨f2, hf2, rfl⟩
    have hfne : f1 ≠ f2 := fun h ↦ hne (congrArg (edgeEmb ell) h)
    convert (rawSpec ell).2.2.1 f1 f2 hf1 hf2 hfne using 1 <;> rfl
  refine ⟨{
    retainedLines := retained
    retainedLines_mem_iff := by
      intro ell
      simp [retained]
    coordinate := coord
    coordinate_injective_on_line := coord_inj
    coordinate_affineCombination := coord_affine
    localEdges := chosenEdges
    localEdges_mem_iff := local_mem
    localEdge_no_point_in_openSegment := by
      intro ell e he p hp
      have hed := (local_mem ell e.1 e.2).mp he
      have hcp := coord_openSegment ell hed.1 hed.2.1 hed.2.2.1 hp
      exact hed.2.2.2 p hcp.2 hcp.1
    distinct_localEdges_openSegment_disjoint := by
      intro ell e1 e2 he1 he2 hne
      have hreal := local_open_disjoint ell e1 e2 he1 he2 hne
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have h1 := (local_mem ell e1.1 e1.2).mp he1
      have h2 := (local_mem ell e2.1 e2.2).mp he2
      exact Set.disjoint_left.mp hreal
        (coord_openSegment ell h1.1 h1.2.1 h1.2.2.1 hz1).1
        (coord_openSegment ell h2.1 h2.2.1 h2.2.2.1 hz2).1
    distinct_localEdges_segment_intersection_subsingleton := by
      intro ell e1 e2 he1 he2 hne
      have hcoord := local_closed_subsingleton ell e1 e2 he1 he2 hne
      have h1 := (local_mem ell e1.1 e1.2).mp he1
      have h2 := (local_mem ell e2.1 e2.2).mp he2
      intro z hz w hw
      have hz1 := coord_segment ell h1.1 h1.2.1 h1.2.2.1 hz.1
      have hz2 := coord_segment ell h2.1 h2.2.1 h2.2.2.1 hz.2
      have hw1 := coord_segment ell h1.1 h1.2.1 h1.2.2.1 hw.1
      have hw2 := coord_segment ell h2.1 h2.2.1 h2.2.2.1 hw.2
      exact coord_inj ell hz1.2 hw1.2
        (hcoord ⟨hz1.1, hz2.1⟩ ⟨hw1.1, hw2.1⟩)
    localEdges_card_add_one := by
      intro ell
      exact local_card ell
  }⟩
