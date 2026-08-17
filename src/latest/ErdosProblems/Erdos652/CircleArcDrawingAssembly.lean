import Submission.GeometricArcDrawing
import ErdosProblems.Erdos652.Circles

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

namespace Erdos652

/-- Assemble the retained successor arcs from an arbitrary finite family of
keyed circles into a drawing.  Different circle keys meet in at most two
points; arcs with the same key have disjoint relative interiors. -/
lemma circleRetainedArcDrawingAssembly
    (V : Finset Point) (C : Finset CircleKey)
    {ι : Type} (A : Finset ι) (endpoint : ι → Sym2 V)
    (center : ι → C)
    (arcStart arcEnd : ι → V)
    (carrier arcInterior : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (γ : ι → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (h_endpoint_eq : ∀ i ∈ A, endpoint i = Sym2.mk (arcStart i) (arcEnd i))
    (h_endpoints_distinct : ∀ i ∈ A,
      (arcStart i : EuclideanSpace ℝ (Fin 2)) ≠
        (arcEnd i : EuclideanSpace ℝ (Fin 2)))
    (h_endpoints_on_circle : ∀ i ∈ A,
      (arcStart i : EuclideanSpace ℝ (Fin 2)) ∈
          circle (center i : CircleKey) ∧
        (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∈
          circle (center i : CircleKey))
    (h_arc_param : ∀ i ∈ A,
      Continuous (γ i) ∧
        Function.Injective (γ i) ∧
          (∀ t, γ i t ∈ circle (center i : CircleKey)) ∧
            γ i ⟨0, by simp⟩ =
              (arcStart i : EuclideanSpace ℝ (Fin 2)) ∧
              γ i ⟨1, by simp⟩ =
                (arcEnd i : EuclideanSpace ℝ (Fin 2)) ∧
                carrier i = Set.range (γ i) ∧
                  arcInterior i =
                    Set.range
                      (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                        γ i
                          ⟨t.1, ⟨le_of_lt t.2.1,
                            le_of_lt t.2.2⟩⟩))
    (h_carrier_circle : ∀ i ∈ A, carrier i ⊆
      circle (center i : CircleKey))
    (h_radius_pos : ∀ i ∈ A, 0 < (center i : CircleKey).2)
    (h_no_vertex_in_interior : ∀ i ∈ A, ∀ v : V,
      (v : EuclideanSpace ℝ (Fin 2)) ∉ arcInterior i)
    (h_same_center_disjoint : ∀ i ∈ A, ∀ j ∈ A,
      center i = center j → i ≠ j →
        arcInterior i ∩ arcInterior j = ∅) :
    ∀ (G : SimpleGraph V) [Fintype G.edgeSet],
      G.edgeFinset = A.image endpoint →
        ∃ D : GeometricArcDrawing G,
          (D.localPairCount : ℝ) ≤ 2 * (C.card : ℝ) ^ 2 := by
-- BODY
  classical
  intro G hGfin hGedge
  letI : Fintype G.edgeSet := hGfin
  have h_rep_exists :
      ∀ e : G.edgeFinset, ∃ i ∈ A, endpoint i = e.1 := by
    intro e
    have he : e.1 ∈ A.image endpoint := by
      simpa [hGedge] using e.2
    exact Finset.mem_image.mp he
  let rep : G.edgeFinset → ι := fun e => (h_rep_exists e).choose
  have rep_mem : ∀ e : G.edgeFinset, rep e ∈ A := by
    intro e
    exact (h_rep_exists e).choose_spec.1
  have rep_endpoint : ∀ e : G.edgeFinset, endpoint (rep e) = e.1 := by
    intro e
    exact (h_rep_exists e).choose_spec.2
  have rep_ne_of_edge_ne :
      ∀ {e₁ e₂ : G.edgeFinset}, e₁ ≠ e₂ → rep e₁ ≠ rep e₂ := by
    intro e₁ e₂ he hrep
    apply he
    apply Subtype.ext
    calc
      e₁.1 = endpoint (rep e₁) := (rep_endpoint e₁).symm
      _ = endpoint (rep e₂) := by rw [hrep]
      _ = e₂.1 := rep_endpoint e₂
  have interior_circle : ∀ i ∈ A, arcInterior i ⊆
      circle (center i : CircleKey) := by
    intro i hi p hp
    rcases h_arc_param i hi with
      ⟨_, _, hcircle, _, _, _, hinterior⟩
    rw [hinterior] at hp
    rcases hp with ⟨t, rfl⟩
    exact hcircle
      ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩
  have pair_intersection_finite :
      ∀ e₁ e₂ : G.edgeFinset, e₁ ≠ e₂ →
        (arcInterior (rep e₁) ∩ arcInterior (rep e₂)).Finite := by
    intro e₁ e₂ he
    by_cases hc : center (rep e₁) = center (rep e₂)
    · have hdisj := h_same_center_disjoint (rep e₁) (rep_mem e₁)
        (rep e₂) (rep_mem e₂) hc (rep_ne_of_edge_ne he)
      simp [hdisj]
    · have hc' : (center (rep e₁) : CircleKey) ≠
          (center (rep e₂) : CircleKey) := by
        intro hcoerce
        exact hc (Subtype.ext hcoerce)
      exact (circle_intersection_atMostTwo hc').1.subset (by
          intro p hp
          exact ⟨interior_circle (rep e₁) (rep_mem e₁) hp.1,
            interior_circle (rep e₂) (rep_mem e₂) hp.2⟩)
  have carrier_not_interior_endpoint :
      ∀ i ∈ A, ∀ {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ carrier i → p ∉ arcInterior i →
          p = (arcStart i : EuclideanSpace ℝ (Fin 2)) ∨
            p = (arcEnd i : EuclideanSpace ℝ (Fin 2)) := by
    intro i hi p hpCarrier hpInterior
    rcases h_arc_param i hi with
      ⟨_, _, _, hstart, hend, hcarrier, hinterior⟩
    rw [hcarrier] at hpCarrier
    rcases hpCarrier with ⟨t, rfl⟩
    by_cases ht0 : t.1 = 0
    · left
      have ht : t = ⟨0, by simp⟩ := Subtype.ext ht0
      simpa [ht] using hstart
    · by_cases ht1 : t.1 = 1
      · right
        have ht : t = ⟨1, by simp⟩ := Subtype.ext ht1
        simpa [ht] using hend
      · exfalso
        apply hpInterior
        rw [hinterior]
        have htpos : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
        have htlt : t.1 < 1 := lt_of_le_of_ne t.2.2 ht1
        refine ⟨⟨t.1, htpos, htlt⟩, ?_⟩
        have ht :
            (⟨t.1, ⟨le_of_lt htpos, le_of_lt htlt⟩⟩ :
              Set.Icc (0 : ℝ) 1) = t := Subtype.ext rfl
        change γ i
            (⟨t.1, ⟨le_of_lt htpos, le_of_lt htlt⟩⟩ :
              Set.Icc (0 : ℝ) 1) = γ i t
        rw [ht]
  let pairIntersectionFinset : G.edgeFinset → G.edgeFinset →
      Finset (EuclideanSpace ℝ (Fin 2)) := fun e₁ e₂ =>
    if h : e₁ = e₂ then ∅
    else (pair_intersection_finite e₁ e₂ h).toFinset
  let allIntersectionPoints : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset G.edgeFinset).biUnion (fun e₁ =>
      (Finset.univ : Finset G.edgeFinset).biUnion (fun e₂ =>
        pairIntersectionFinset e₁ e₂))
  let D : GeometricArcDrawing G :=
    { vertexPlacement := fun v => (v : EuclideanSpace ℝ (Fin 2))
      vertexPlacement_injective := by
        intro u v huv
        exact Subtype.ext huv
      edgeSource := fun e => (arcStart (rep e) : EuclideanSpace ℝ (Fin 2))
      edgeTarget := fun e => (arcEnd (rep e) : EuclideanSpace ℝ (Fin 2))
      edgeCarrier := fun e => carrier (rep e)
      edgeRelativeInterior := fun e => arcInterior (rep e)
      edgeArc_endpoints := by
        intro e
        refine ⟨arcStart (rep e), arcEnd (rep e), ?_, ?_, ?_⟩
        · have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
          have heq : e.1 = Sym2.mk (arcStart (rep e)) (arcEnd (rep e)) := by
            calc
              e.1 = endpoint (rep e) := (rep_endpoint e).symm
              _ = Sym2.mk (arcStart (rep e)) (arcEnd (rep e)) :=
                h_endpoint_eq (rep e) (rep_mem e)
          have hmk : Sym2.mk (arcStart (rep e)) (arcEnd (rep e)) ∈ G.edgeSet := by
            simpa [heq] using hedge
          exact (SimpleGraph.mem_edgeSet G).mp hmk
        · calc
            e.1 = endpoint (rep e) := (rep_endpoint e).symm
            _ = Sym2.mk (arcStart (rep e)) (arcEnd (rep e)) :=
              h_endpoint_eq (rep e) (rep_mem e)
        · exact Or.inl ⟨rfl, rfl⟩
      edge_is_simple_lineSegment_or_circularArc := by
        intro e
        right
        rcases h_arc_param (rep e) (rep_mem e) with
          ⟨hcont, hinj, hcircle, hstart, hend, hcarrier, hinterior⟩
        refine ⟨(center (rep e) : CircleKey).1,
          (center (rep e) : CircleKey).2,
          γ (rep e), h_radius_pos (rep e) (rep_mem e), hcont, hinj, ?_, hstart, hend,
          hcarrier, hinterior⟩
        intro t
        exact hcircle t
      no_vertex_in_edge_interior := by
        intro v e
        exact h_no_vertex_in_interior (rep e) (rep_mem e) v
      no_shared_nondegenerate_subarc := by
        intro e₁ e₂ he
        rintro ⟨η, hηcont, hηinj, hηnondeg, hηrange⟩
        by_cases hc : center (rep e₁) = center (rep e₂)
        · have hrepne : rep e₁ ≠ rep e₂ := rep_ne_of_edge_ne he
          have hdisj := h_same_center_disjoint (rep e₁) (rep_mem e₁)
            (rep e₂) (rep_mem e₂) hc hrepne
          let Epts : Set (EuclideanSpace ℝ (Fin 2)) :=
            {(arcStart (rep e₁) : EuclideanSpace ℝ (Fin 2)),
              (arcEnd (rep e₁) : EuclideanSpace ℝ (Fin 2)),
              (arcStart (rep e₂) : EuclideanSpace ℝ (Fin 2)),
              (arcEnd (rep e₂) : EuclideanSpace ℝ (Fin 2))}
          let EptsFinset : Finset (EuclideanSpace ℝ (Fin 2)) :=
            {(arcStart (rep e₁) : EuclideanSpace ℝ (Fin 2)),
              (arcEnd (rep e₁) : EuclideanSpace ℝ (Fin 2)),
              (arcStart (rep e₂) : EuclideanSpace ℝ (Fin 2)),
              (arcEnd (rep e₂) : EuclideanSpace ℝ (Fin 2))}
          have hEpts_eq :
              Epts = (EptsFinset : Set (EuclideanSpace ℝ (Fin 2))) := by
            ext p
            simp [Epts, EptsFinset]
          have hEptsFinite : Epts.Finite := by
            rw [hEpts_eq]
            exact Finset.finite_toSet EptsFinset
          have hEptsCard : Epts.ncard ≤ 4 := by
            rw [hEpts_eq, Set.ncard_coe_finset]
            simpa [EptsFinset] using
              (Finset.card_le_four
                (a := (arcStart (rep e₁) : EuclideanSpace ℝ (Fin 2)))
                (b := (arcEnd (rep e₁) : EuclideanSpace ℝ (Fin 2)))
                (c := (arcStart (rep e₂) : EuclideanSpace ℝ (Fin 2)))
                (d := (arcEnd (rep e₂) : EuclideanSpace ℝ (Fin 2))))
          have hηEpts : Set.range η ⊆ Epts := by
            intro p hp
            have hcar := hηrange hp
            by_cases hp₁ : p ∈ arcInterior (rep e₁)
            · have hp₂not : p ∉ arcInterior (rep e₂) := by
                intro hp₂
                have hpBoth : p ∈ arcInterior (rep e₁) ∩ arcInterior (rep e₂) :=
                  ⟨hp₁, hp₂⟩
                simp [hdisj] at hpBoth
              rcases carrier_not_interior_endpoint (rep e₂) (rep_mem e₂)
                  hcar.2 hp₂not with hpStart | hpEnd
              · simp [Epts, hpStart]
              · simp [Epts, hpEnd]
            · rcases carrier_not_interior_endpoint (rep e₁) (rep_mem e₁)
                  hcar.1 hp₁ with hpStart | hpEnd
              · simp [Epts, hpStart]
              · simp [Epts, hpEnd]
          let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
          let tq : Set.Icc (0 : ℝ) 1 := ⟨(1 / 4 : ℝ), by norm_num⟩
          let tm : Set.Icc (0 : ℝ) 1 := ⟨(1 / 2 : ℝ), by norm_num⟩
          let tt : Set.Icc (0 : ℝ) 1 := ⟨(3 / 4 : ℝ), by norm_num⟩
          let t1 : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
          have image_ne {s t : Set.Icc (0 : ℝ) 1} (hst : s ≠ t) :
              η s ≠ η t := by
            intro hη
            exact hst (hηinj hη)
          have ht0q : t0 ≠ tq := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [t0, tq] at hv
          have ht0m : t0 ≠ tm := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [t0, tm] at hv
          have ht0t : t0 ≠ tt := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [t0, tt] at hv
          have ht01 : t0 ≠ t1 := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [t0, t1] at hv
          have htqm : tq ≠ tm := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [tq, tm] at hv
          have htqt : tq ≠ tt := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [tq, tt] at hv
          have htq1 : tq ≠ t1 := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [tq, t1] at hv
          have htmt : tm ≠ tt := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [tm, tt] at hv
          have htm1 : tm ≠ t1 := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [tm, t1] at hv
          have htt1 : tt ≠ t1 := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [tt, t1] at hv
          have hη0q : η t0 ≠ η tq := image_ne ht0q
          have hη0m : η t0 ≠ η tm := image_ne ht0m
          have hη0t : η t0 ≠ η tt := image_ne ht0t
          have hη01 : η t0 ≠ η t1 := image_ne ht01
          have hηqm : η tq ≠ η tm := image_ne htqm
          have hηqt : η tq ≠ η tt := image_ne htqt
          have hηq1 : η tq ≠ η t1 := image_ne htq1
          have hηmt : η tm ≠ η tt := image_ne htmt
          have hηm1 : η tm ≠ η t1 := image_ne htm1
          have hηt1 : η tt ≠ η t1 := image_ne htt1
          let U : Set (EuclideanSpace ℝ (Fin 2)) :=
            {η t0, η tq, η tm, η tt, η t1}
          have hUsub : U ⊆ Epts := by
            intro p hp
            simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl
            · exact hηEpts (Set.mem_range_self t0)
            · exact hηEpts (Set.mem_range_self tq)
            · exact hηEpts (Set.mem_range_self tm)
            · exact hηEpts (Set.mem_range_self tt)
            · exact hηEpts (Set.mem_range_self t1)
          have hUcard : U.ncard = 5 := by
            simp [U, hη0q, hη0m, hη0t, hη01, hηqm,
              hηqt, hηq1, hηmt, hηm1, hηt1]
          have hcard_le : U.ncard ≤ Epts.ncard :=
            Set.ncard_le_ncard hUsub hEptsFinite
          omega
        · have hc' : (center (rep e₁) : CircleKey) ≠
              (center (rep e₂) : CircleKey) := by
            intro hcoerce
            exact hc (Subtype.ext hcoerce)
          let S : Set Point :=
            circle (center (rep e₁) : CircleKey) ∩
              circle (center (rep e₂) : CircleKey)
          have hSfin : S.Finite := (circle_intersection_atMostTwo hc').1
          have hSncard : S.ncard ≤ 2 := (circle_intersection_atMostTwo hc').2
          have hηS : Set.range η ⊆ S := by
            intro p hp
            rcases hp with ⟨t, rfl⟩
            have hcar := hηrange (Set.mem_range_self t)
            exact ⟨h_carrier_circle (rep e₁) (rep_mem e₁) hcar.1,
              h_carrier_circle (rep e₂) (rep_mem e₂) hcar.2⟩
          let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
          let tm : Set.Icc (0 : ℝ) 1 := ⟨(1 / 2 : ℝ), by norm_num⟩
          let t1 : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
          have ht0m : t0 ≠ tm := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [t0, tm] at hv
          have ht01 : t0 ≠ t1 := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [t0, t1] at hv
          have htm1 : tm ≠ t1 := by
            intro h
            have hv := congrArg Subtype.val h
            norm_num [tm, t1] at hv
          have hη0m : η t0 ≠ η tm := by
            intro h
            exact ht0m (hηinj h)
          have hη01 : η t0 ≠ η t1 := by
            intro h
            exact ht01 (hηinj h)
          have hηm1 : η tm ≠ η t1 := by
            intro h
            exact htm1 (hηinj h)
          let T : Set (EuclideanSpace ℝ (Fin 2)) := {η t0, η tm, η t1}
          have hTsub : T ⊆ S := by
            intro p hp
            simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
            rcases hp with rfl | rfl | rfl
            · exact hηS (Set.mem_range_self t0)
            · exact hηS (Set.mem_range_self tm)
            · exact hηS (Set.mem_range_self t1)
          have hTcard : T.ncard = 3 := by
            simp [T, hη0m, hη01, hηm1]
          have hcard_le : T.ncard ≤ S.ncard :=
            Set.ncard_le_ncard hTsub hSfin
          omega
      intersectionPoints := allIntersectionPoints
      intersectionPoints_spec := by
        intro p
        constructor
        · intro hp
          simp only [allIntersectionPoints, Finset.mem_biUnion,
            Finset.mem_univ, true_and] at hp
          rcases hp with ⟨e₁, e₂, hpPair⟩
          by_cases heq : e₁ = e₂
          · simp [pairIntersectionFinset, heq] at hpPair
          · have hpSet :
                p ∈ arcInterior (rep e₁) ∩ arcInterior (rep e₂) := by
              exact (Set.Finite.mem_toFinset
                (pair_intersection_finite e₁ e₂ heq)).mp
                  (by simpa [pairIntersectionFinset, heq] using hpPair)
            exact ⟨e₁, e₂, heq, hpSet.1, hpSet.2⟩
        · intro hp
          rcases hp with ⟨e₁, e₂, he, hp₁, hp₂⟩
          simp only [allIntersectionPoints, Finset.mem_biUnion,
            Finset.mem_univ, true_and]
          refine ⟨e₁, e₂, ?_⟩
          exact (by
            have hpSet :
                p ∈ (pair_intersection_finite e₁ e₂ he).toFinset :=
              (Set.Finite.mem_toFinset
                (pair_intersection_finite e₁ e₂ he)).mpr ⟨hp₁, hp₂⟩
            simpa [pairIntersectionFinset, he] using hpSet)
      localPairCount :=
        allIntersectionPoints.sum (fun p =>
          Nat.choose (((Finset.univ : Finset G.edgeFinset).filter
            (fun e => p ∈ arcInterior (rep e))).card) 2)
      localPairCount_eq := by
        rfl }
  refine ⟨D, ?_⟩
  let incident : EuclideanSpace ℝ (Fin 2) → Finset G.edgeFinset := fun p =>
    (Finset.univ : Finset G.edgeFinset).filter
      (fun e => p ∈ arcInterior (rep e))
  have edge_eq_of_same_center_of_mem :
      ∀ {e₁ e₂ : G.edgeFinset} {p : EuclideanSpace ℝ (Fin 2)},
        center (rep e₁) = center (rep e₂) →
          p ∈ arcInterior (rep e₁) →
            p ∈ arcInterior (rep e₂) → e₁ = e₂ := by
    intro e₁ e₂ p hc hp₁ hp₂
    by_contra he
    have hdisj := h_same_center_disjoint (rep e₁) (rep_mem e₁)
      (rep e₂) (rep_mem e₂) hc (rep_ne_of_edge_ne he)
    have hpBoth : p ∈ arcInterior (rep e₁) ∩ arcInterior (rep e₂) :=
      ⟨hp₁, hp₂⟩
    simpa [hdisj] using hpBoth
  have centers_distinct_of_local_pair :
      ∀ {e₁ e₂ : G.edgeFinset} {p : EuclideanSpace ℝ (Fin 2)},
        e₁ ≠ e₂ →
          p ∈ arcInterior (rep e₁) →
            p ∈ arcInterior (rep e₂) →
              (center (rep e₁) : CircleKey) ≠
                (center (rep e₂) : CircleKey) := by
    intro e₁ e₂ p he hp₁ hp₂ hcenters
    apply he
    exact edge_eq_of_same_center_of_mem
      (Subtype.ext hcenters) hp₁ hp₂
  let localOrdered :
      Finset (Sigma fun _p : EuclideanSpace ℝ (Fin 2) =>
        G.edgeFinset × G.edgeFinset) :=
    allIntersectionPoints.sigma (fun p => (incident p).offDiag)
  let centerIntersectionFinset : C × C →
      Finset (EuclideanSpace ℝ (Fin 2)) := fun cp =>
    if h : cp.1 = cp.2 then
      ∅
    else
      ((circle_intersection_atMostTwo (by
        intro hval
        exact h (Subtype.ext hval))).1).toFinset
  let centerPointFinset :
      Finset (Sigma fun _cp : C × C => EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset (C × C)).sigma centerIntersectionFinset
  let centerPoint :
      (Sigma fun _p : EuclideanSpace ℝ (Fin 2) =>
        G.edgeFinset × G.edgeFinset) →
        (Sigma fun _cp : C × C => EuclideanSpace ℝ (Fin 2)) := fun x =>
    ⟨(center (rep x.2.1), center (rep x.2.2)), x.1⟩
  have choose_le_offDiag_card :
      ∀ s : Finset G.edgeFinset, Nat.choose s.card 2 ≤ s.offDiag.card := by
    intro s
    have hcard :
        s.card * s.card - s.card = s.card * (s.card - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    rw [Finset.offDiag_card, hcard, Nat.choose_two_right]
    exact Nat.div_le_self _ _
  have h_local_le_ordered : D.localPairCount ≤ localOrdered.card := by
    rw [D.localPairCount_eq]
    change
      allIntersectionPoints.sum (fun p =>
        Nat.choose (incident p).card 2) ≤ localOrdered.card
    rw [Finset.card_sigma]
    exact Finset.sum_le_sum (by
      intro p hp
      exact choose_le_offDiag_card (incident p))
  have h_centerPoint_maps :
      Set.MapsTo centerPoint (localOrdered : Set
        (Sigma fun _p : EuclideanSpace ℝ (Fin 2) =>
          G.edgeFinset × G.edgeFinset)) centerPointFinset := by
    intro x hx
    have hx' := (Finset.mem_sigma.mp hx).2
    have hxedges := (Finset.mem_offDiag.mp hx')
    have hp₁ : x.1 ∈ arcInterior (rep x.2.1) := by
      simpa [incident] using hxedges.1
    have hp₂ : x.1 ∈ arcInterior (rep x.2.2) := by
      simpa [incident] using hxedges.2.1
    have hcenters :
        (center (rep x.2.1) : CircleKey) ≠
          (center (rep x.2.2) : CircleKey) :=
      centers_distinct_of_local_pair hxedges.2.2 hp₁ hp₂
    have hcentersSubtype :
        center (rep x.2.1) ≠ center (rep x.2.2) := by
      intro h
      exact hcenters (congrArg Subtype.val h)
    have hpCircle :
        x.1 ∈ circle (center (rep x.2.1) : CircleKey) ∧
          x.1 ∈ circle (center (rep x.2.2) : CircleKey) :=
      ⟨interior_circle (rep x.2.1) (rep_mem x.2.1) hp₁,
        interior_circle (rep x.2.2) (rep_mem x.2.2) hp₂⟩
    have hpFinset :
        x.1 ∈ ((circle_intersection_atMostTwo hcenters).1).toFinset :=
      (Set.Finite.mem_toFinset
        ((circle_intersection_atMostTwo hcenters).1)).mpr hpCircle
    simpa [centerPointFinset, centerPoint, centerIntersectionFinset,
      hcentersSubtype] using hpFinset
  have h_centerPoint_inj :
      Set.InjOn centerPoint (localOrdered : Set
        (Sigma fun _p : EuclideanSpace ℝ (Fin 2) =>
          G.edgeFinset × G.edgeFinset)) := by
    intro x hx y hy hxy
    have hxedges := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hx).2
    have hyedges := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hy).2
    have hx₁ : x.1 ∈ arcInterior (rep x.2.1) := by
      simpa [incident] using hxedges.1
    have hx₂ : x.1 ∈ arcInterior (rep x.2.2) := by
      simpa [incident] using hxedges.2.1
    have hy₁ : y.1 ∈ arcInterior (rep y.2.1) := by
      simpa [incident] using hyedges.1
    have hy₂ : y.1 ∈ arcInterior (rep y.2.2) := by
      simpa [incident] using hyedges.2.1
    have hxy_parts := Sigma.ext_iff.mp hxy
    have hcenters₁ :
        center (rep x.2.1) = center (rep y.2.1) := by
      exact congrArg Prod.fst hxy_parts.1
    have hcenters₂ :
        center (rep x.2.2) = center (rep y.2.2) := by
      exact congrArg Prod.snd hxy_parts.1
    have hp : x.1 = y.1 := eq_of_heq hxy_parts.2
    have he₁ : x.2.1 = y.2.1 := by
      exact edge_eq_of_same_center_of_mem hcenters₁ hx₁ (by
        simpa [← hp] using hy₁)
    have he₂ : x.2.2 = y.2.2 := by
      exact edge_eq_of_same_center_of_mem hcenters₂ hx₂ (by
        simpa [← hp] using hy₂)
    exact Sigma.ext hp (heq_of_eq (Prod.ext he₁ he₂))
  have h_ordered_le_center :
      localOrdered.card ≤ centerPointFinset.card :=
    Finset.card_le_card_of_injOn centerPoint h_centerPoint_maps
      h_centerPoint_inj
  have h_center_card : centerPointFinset.card ≤ 2 * C.card ^ 2 := by
    rw [Finset.card_sigma]
    calc
      (∑ cp ∈ (Finset.univ : Finset (C × C)),
          (centerIntersectionFinset cp).card)
          ≤ ∑ _cp ∈ (Finset.univ : Finset (C × C)), 2 := by
            exact Finset.sum_le_sum (by
              intro cp hcp
              by_cases h : cp.1 = cp.2
              · simp [centerIntersectionFinset, h]
              · have hval : (cp.1 : CircleKey) ≠ (cp.2 : CircleKey) := by
                  intro hval
                  exact h (Subtype.ext hval)
                let S : Set Point := circle (cp.1 : CircleKey) ∩ circle (cp.2 : CircleKey)
                have hSfin : S.Finite := (circle_intersection_atMostTwo hval).1
                have hSncard : S.ncard ≤ 2 := (circle_intersection_atMostTwo hval).2
                have hScard : hSfin.toFinset.card ≤ 2 := by
                  rw [← Set.ncard_eq_toFinset_card S hSfin]
                  exact hSncard
                simpa [centerIntersectionFinset, h, S] using hScard)
      _ = 2 * C.card ^ 2 := by
        simp [Fintype.card_prod, Fintype.card_coe, pow_two]
        omega
  have h_nat : D.localPairCount ≤ 2 * C.card ^ 2 :=
    h_local_le_ordered.trans (h_ordered_le_center.trans h_center_card)
  exact_mod_cast h_nat

end Erdos652
