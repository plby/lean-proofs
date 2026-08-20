import ErdosProblems.Erdos733.ST.LinearCrossingInequality
import ErdosProblems.Erdos733.ST.CrossingNumber
import ErdosProblems.Erdos733.ST.NatSInfRangeAttained
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawingNonempty
import ErdosProblems.Erdos733.ST.InducedSubdrawingBridge
import ErdosProblems.Erdos733.ST.NoAdjacentMinimalDrawing
import ErdosProblems.Erdos733.ST.FinitePowersetBernoulliFamilyMoment

open Classical
open scoped Real
noncomputable section

-- [TABLET NODE: CrossingLemma]
theorem CrossingLemma {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet]
    (hn : 1 ≤ Fintype.card V)
    (he : 4 * Fintype.card V ≤ G.edgeFinset.card) :
    (G.edgeFinset.card : ℝ) ^ 3 / (100 * (Fintype.card V : ℝ) ^ 2) ≤
      (CrossingNumber G : ℝ) := by
-- BODY
  classical
  let N : ℝ := Fintype.card V
  let E : ℝ := G.edgeFinset.card
  let p : ℝ := 4 * N / E
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hFourNE : 4 * N ≤ E := by
    dsimp [N, E]
    exact_mod_cast he
  have hEpos : 0 < E := lt_of_lt_of_le (by positivity) hFourNE
  have hpPos : 0 < p := by
    dsimp [p]
    positivity
  have hpNonneg : 0 ≤ p := hpPos.le
  have hpLeOne : p ≤ 1 := by
    rw [show p = 4 * N / E by rfl, div_le_one hEpos]
    exact hFourNE
  have hOneSubNonneg : 0 ≤ 1 - p := sub_nonneg.mpr hpLeOne

  obtain ⟨D, hDcross, hDadj⟩ := NoAdjacentMinimalDrawing G
  let CrossingPoint := {q // q ∈ D.crossingSet}
  let firstEdge : CrossingPoint → G.edgeFinset := fun q =>
    Classical.choose ((D.crossingSet_spec q.1).mp q.2)
  let secondEdge : CrossingPoint → G.edgeFinset := fun q =>
    Classical.choose
      (Classical.choose_spec ((D.crossingSet_spec q.1).mp q.2))
  have crossingEdgeSpec :
      ∀ q : CrossingPoint,
        firstEdge q ≠ secondEdge q ∧
          q.1 ∈ (D.edgeArc (firstEdge q)).relativeInterior ∧
            q.1 ∈ (D.edgeArc (secondEdge q)).relativeInterior := by
    intro q
    exact Classical.choose_spec
      (Classical.choose_spec ((D.crossingSet_spec q.1).mp q.2))
  let crossingSupport : CrossingPoint → Finset V := fun q =>
    (firstEdge q).1.toFinset ∪ (secondEdge q).1.toFinset

  obtain ⟨_Duniv, _hDunivVertices, _hDunivEdges, _hDunivCrossings,
      hCrossingEdgesDisjoint⟩ :=
    InducedSubdrawingBridge G D (Set.univ : Set V)
  have hCrossingSupportCard :
      ∀ q : CrossingPoint, (crossingSupport q).card = 4 := by
    intro q
    have hdisjoint :
        Disjoint (firstEdge q).1.toFinset (secondEdge q).1.toFinset := by
      apply Finset.disjoint_left.mpr
      intro v hvFirst hvSecond
      have hvFirst' : v ∈ (firstEdge q).1 :=
        Sym2.mem_toFinset.mp hvFirst
      have hvSecond' : v ∈ (secondEdge q).1 :=
        Sym2.mem_toFinset.mp hvSecond
      rcases crossingEdgeSpec q with ⟨hne, hqFirst, hqSecond⟩
      exact (hCrossingEdgesDisjoint hDadj hne hqFirst hqSecond
        ⟨v, hvFirst', hvSecond'⟩).elim
    dsimp [crossingSupport]
    rw [Finset.card_union_of_disjoint hdisjoint,
      G.card_toFinset_mem_edgeFinset (firstEdge q),
      G.card_toFinset_mem_edgeFinset (secondEdge q)]

  let retainedCrossings (X : Finset V) : Finset CrossingPoint :=
    (Finset.univ : Finset CrossingPoint).filter
      (fun q => crossingSupport q ⊆ X)
  let weight (X : Finset V) : ℝ :=
    p ^ X.card * (1 - p) ^ ((Finset.univ : Finset V) \ X).card

  have hVertexMoment :
      ∑ X ∈ (Finset.univ : Finset V).powerset,
          weight X * (X.card : ℝ) = N * p := by
    have h := FinitePowersetBernoulliFamilyMoment
      (Finset.univ : Finset V) (Finset.univ : Finset V)
      (fun v : V => ({v} : Finset V)) (by simp) p
    simpa [weight, N, Finset.singleton_subset_iff] using h

  have hEdgeMoment :
      ∑ X ∈ (Finset.univ : Finset V).powerset,
          weight X *
            ((G.edgeFinset.filter fun e => e.toFinset ⊆ X).card : ℝ) =
        E * p ^ 2 := by
    have h := FinitePowersetBernoulliFamilyMoment
      (Finset.univ : Finset V) G.edgeFinset
      (fun e : Sym2 V => e.toFinset) (by simp) p
    calc
      _ = ∑ e ∈ G.edgeFinset, p ^ e.toFinset.card := by
        simpa [weight] using h
      _ = ∑ _e ∈ G.edgeFinset, p ^ 2 := by
        apply Finset.sum_congr rfl
        intro e heG
        rw [G.card_toFinset_mem_edgeFinset ⟨e, heG⟩]
      _ = E * p ^ 2 := by simp [E]

  have hCrossingMoment :
      ∑ X ∈ (Finset.univ : Finset V).powerset,
          weight X * (retainedCrossings X).card =
        (CrossingNumber G : ℝ) * p ^ 4 := by
    have h := FinitePowersetBernoulliFamilyMoment
      (Finset.univ : Finset V) (Finset.univ : Finset CrossingPoint)
      crossingSupport (by simp) p
    calc
      _ = ∑ q : CrossingPoint, p ^ (crossingSupport q).card := by
        simpa [weight, retainedCrossings] using h
      _ = ∑ _q : CrossingPoint, p ^ 4 := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [hCrossingSupportCard q]
      _ = (CrossingNumber G : ℝ) * p ^ 4 := by
        simp [CrossingPoint, hDcross]

  have hPointwise :
      ∀ X ∈ (Finset.univ : Finset V).powerset,
        ((G.edgeFinset.filter fun e => e.toFinset ⊆ X).card : ℝ) -
            3 * (X.card : ℝ) ≤
          (retainedCrossings X).card := by
    intro X _hX
    obtain ⟨DX, _hDXVertices, _hDXEdges, hDXCrossings, _hDXDisjoint⟩ :=
      InducedSubdrawingBridge G D (X : Set V)
    have hInduceVal :
        (⇑(SimpleGraph.Embedding.induce (G := G) (X : Set V)) :
          (↥(X : Set V)) → V) = Subtype.val := by
      rfl
    have hInduceHomVal :
        (⇑(SimpleGraph.Embedding.induce (G := G) (X : Set V)).toHom :
          (↥(X : Set V)) → V) = Subtype.val := by
      rfl

    have hInducedEdgeCard :
        (G.induce (X : Set V)).edgeFinset.card =
          (G.edgeFinset.filter fun e => e.toFinset ⊆ X).card := by
      apply Finset.card_bij
          (fun ed _hed =>
            Sym2.map (Subtype.val : (↥(X : Set V)) → V) ed)
      · intro ed hed
        apply Finset.mem_filter.mpr
        constructor
        · apply SimpleGraph.mem_edgeFinset.mpr
          have hmap :=
            (SimpleGraph.Embedding.induce (G := G) (X : Set V)).toHom.map_mem_edgeSet
              (SimpleGraph.mem_edgeFinset.mp hed)
          rw [hInduceHomVal] at hmap
          exact hmap
        · intro v hv
          rw [Sym2.mem_toFinset] at hv
          rcases Sym2.mem_map.mp hv with ⟨a, _ha, rfl⟩
          exact a.2
      · intro ed₁ _hed₁ ed₂ _hed₂ hmap
        exact Sym2.map.injective
          (Subtype.val_injective : Function.Injective
            (Subtype.val : (↥(X : Set V)) → V)) hmap
      · intro eOld heOld
        rcases Finset.mem_filter.mp heOld with ⟨heG, heX⟩
        have hends : ∀ v : V, v ∈ eOld → v ∈ (X : Set V) := by
          intro v hv
          exact heX (Sym2.mem_toFinset.mpr hv)
        let ed : Sym2 (↥(X : Set V)) := eOld.attachWith hends
        refine ⟨ed, ?_, ?_⟩
        · apply SimpleGraph.mem_edgeFinset.mpr
          apply (SimpleGraph.Embedding.induce
            (G := G) (X : Set V)).map_mem_edgeSet_iff.mp
          rw [hInduceVal]
          simpa [ed, Sym2.attachWith_map_subtypeVal] using
            (SimpleGraph.mem_edgeFinset.mp heG)
        · simpa [ed, Sym2.attachWith_map_subtypeVal]

    let oldPoint : DX.crossingSet → CrossingPoint := fun z =>
      ⟨z.1, by
        rcases (hDXCrossings z.1).mp z.2 with
          ⟨e₁, e₂, h₁₂, _hX₁, _hX₂, hz₁, hz₂⟩
        exact (D.crossingSet_spec z.1).2 ⟨e₁, e₂, h₁₂, hz₁, hz₂⟩⟩
    have holdPointRetained :
        ∀ z : DX.crossingSet, crossingSupport (oldPoint z) ⊆ X := by
      intro z v hv
      rcases (hDXCrossings z.1).mp z.2 with
        ⟨e₁, e₂, h₁₂, hX₁, hX₂, hz₁, hz₂⟩
      have hFirst : firstEdge (oldPoint z) = e₁ ∨ firstEdge (oldPoint z) = e₂ := by
        by_contra hne
        rw [not_or] at hne
        rcases crossingEdgeSpec (oldPoint z) with
          ⟨_hFirstSecond, hzFirst, _hzSecond⟩
        exact D.no_three_edge_interiors_meet
          hne.1 hne.2 h₁₂ hzFirst hz₁ hz₂
      have hSecond : secondEdge (oldPoint z) = e₁ ∨ secondEdge (oldPoint z) = e₂ := by
        by_contra hne
        rw [not_or] at hne
        rcases crossingEdgeSpec (oldPoint z) with
          ⟨_hFirstSecond, _hzFirst, hzSecond⟩
        exact D.no_three_edge_interiors_meet
          hne.1 hne.2 h₁₂ hzSecond hz₁ hz₂
      simp only [crossingSupport, Finset.mem_union] at hv
      rcases hv with hv | hv
      · have hv' : v ∈ (firstEdge (oldPoint z)).1 :=
          Sym2.mem_toFinset.mp hv
        rcases hFirst with h | h
        · exact hX₁ v (h ▸ hv')
        · exact hX₂ v (h ▸ hv')
      · have hv' : v ∈ (secondEdge (oldPoint z)).1 :=
          Sym2.mem_toFinset.mp hv
        rcases hSecond with h | h
        · exact hX₁ v (h ▸ hv')
        · exact hX₂ v (h ▸ hv')
    have hDXCrossingCard :
        DX.crossingSet.card ≤ (retainedCrossings X).card := by
      let f : DX.crossingSet → retainedCrossings X := fun z =>
        ⟨oldPoint z, by
          simp only [retainedCrossings, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact holdPointRetained z⟩
      apply Finset.card_le_card_of_injective (f := f)
      intro z₁ z₂ hz
      apply Subtype.ext
      exact congrArg (fun t : retainedCrossings X => (t.1 : CrossingPoint).1) hz

    have hLinear := LinearCrossingInequality (G.induce (X : Set V))
    have hnonempty :
        Nonempty (OrdinaryPolygonalDrawing (G.induce (X : Set V))) :=
      OrdinaryPolygonalDrawingNonempty (G.induce (X : Set V))
    have hattainment :
        ∃ D : OrdinaryPolygonalDrawing (G.induce (X : Set V)),
          D.crossingSet.card = CrossingNumber (G.induce (X : Set V)) ∧
            ∀ D' : OrdinaryPolygonalDrawing (G.induce (X : Set V)),
              CrossingNumber (G.induce (X : Set V)) ≤ D'.crossingSet.card := by
      simpa [CrossingNumber] using
        (NatSInfRangeAttained
          (α := OrdinaryPolygonalDrawing (G.induce (X : Set V)))
          (fun D : OrdinaryPolygonalDrawing (G.induce (X : Set V)) =>
            D.crossingSet.card)
          hnonempty)
    rcases hattainment with ⟨_Dmin, ⟨_hDminCross, hMinimum⟩⟩
    have hCrossingNumberLe :
        CrossingNumber (G.induce (X : Set V)) ≤ DX.crossingSet.card :=
      hMinimum DX
    have hInteger :
        ((G.induce (X : Set V)).edgeFinset.card : ℤ) -
            3 * (Fintype.card (↥(X : Set V)) : ℤ) ≤
          (DX.crossingSet.card : ℤ) := by
      exact hLinear.trans (by exact_mod_cast hCrossingNumberLe)
    have hReal :
        ((G.induce (X : Set V)).edgeFinset.card : ℝ) -
            3 * (X.card : ℝ) ≤
          (DX.crossingSet.card : ℝ) := by
      rw [← Fintype.card_coe X]
      exact_mod_cast hInteger
    rw [hInducedEdgeCard] at hReal
    exact hReal.trans (by exact_mod_cast hDXCrossingCard)

  have hWeighted :
      ∑ X ∈ (Finset.univ : Finset V).powerset,
          weight X *
            (((G.edgeFinset.filter fun e => e.toFinset ⊆ X).card : ℝ) -
              3 * (X.card : ℝ)) ≤
        ∑ X ∈ (Finset.univ : Finset V).powerset,
          weight X * (retainedCrossings X).card := by
    apply Finset.sum_le_sum
    intro X hX
    apply mul_le_mul_of_nonneg_left (hPointwise X hX)
    dsimp [weight]
    exact mul_nonneg (pow_nonneg hpNonneg _) (pow_nonneg hOneSubNonneg _)

  have hMomentInequality :
      E * p ^ 2 - 3 * (N * p) ≤
        (CrossingNumber G : ℝ) * p ^ 4 := by
    calc
      E * p ^ 2 - 3 * (N * p) =
          ∑ X ∈ (Finset.univ : Finset V).powerset,
            weight X *
              (((G.edgeFinset.filter fun e => e.toFinset ⊆ X).card : ℝ) -
                3 * (X.card : ℝ)) := by
        rw [← hEdgeMoment, ← hVertexMoment]
        rw [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro X _hX
        ring
      _ ≤ ∑ X ∈ (Finset.univ : Finset V).powerset,
          weight X * (retainedCrossings X).card := hWeighted
      _ = (CrossingNumber G : ℝ) * p ^ 4 := hCrossingMoment

  have hpRelation : E * p = 4 * N := by
    dsimp [p]
    field_simp
  have hNp : N * p ≤ (CrossingNumber G : ℝ) * p ^ 4 := by
    calc
      N * p = E * p ^ 2 - 3 * (N * p) := by
        nlinarith [hpRelation]
      _ ≤ (CrossingNumber G : ℝ) * p ^ 4 := hMomentInequality
  have hNle : N ≤ (CrossingNumber G : ℝ) * p ^ 3 := by
    apply (mul_le_mul_iff_of_pos_left hpPos).mp
    calc
      p * N = N * p := by ring
      _ ≤ (CrossingNumber G : ℝ) * p ^ 4 := hNp
      _ = p * ((CrossingNumber G : ℝ) * p ^ 3) := by ring
  have hpCube : E ^ 3 * p ^ 3 = 64 * N ^ 3 := by
    dsimp [p]
    field_simp
    ring
  have hStrongTimesN :
      E ^ 3 * N ≤ 64 * (CrossingNumber G : ℝ) * N ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hNle (pow_nonneg hEpos.le 3)
    calc
      E ^ 3 * N ≤ E ^ 3 * ((CrossingNumber G : ℝ) * p ^ 3) := hmul
      _ = (CrossingNumber G : ℝ) * (E ^ 3 * p ^ 3) := by ring
      _ = 64 * (CrossingNumber G : ℝ) * N ^ 3 := by rw [hpCube]; ring
  have hStrong : E ^ 3 ≤ 64 * N ^ 2 * (CrossingNumber G : ℝ) := by
    nlinarith [hStrongTimesN]
  have hCrossNonneg : 0 ≤ (CrossingNumber G : ℝ) := by positivity
  have hScaleNonneg : 0 ≤ N ^ 2 * (CrossingNumber G : ℝ) :=
    mul_nonneg (sq_nonneg N) hCrossNonneg
  have hDenomPos : 0 < 100 * N ^ 2 := by positivity
  rw [show (G.edgeFinset.card : ℝ) = E by rfl,
    show (Fintype.card V : ℝ) = N by rfl]
  apply (div_le_iff₀ hDenomPos).2
  nlinarith [hStrong, hScaleNonneg]
