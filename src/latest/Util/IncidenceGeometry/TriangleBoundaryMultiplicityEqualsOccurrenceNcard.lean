import Mathlib.Data.Set.Card.Arithmetic
import Util.IncidenceGeometry.CyclicPresentationTriangleGeneralPosition
import Util.IncidenceGeometry.TriangleBoundaryCyclicIntersectionMultiplicity
import Util.IncidenceGeometry.TriangleBoundaryCyclicIntersectionOccurrenceSet

open Classical
noncomputable section

lemma TriangleBoundaryMultiplicityEqualsOccurrenceNcard
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K)
    (z a b : EuclideanSpace ℝ (Fin 2))
    (hgp : CyclicPresentationTriangleGeneralPosition R z a b) :
    TriangleBoundaryCyclicIntersectionMultiplicity R z a b =
      Set.ncard (TriangleBoundaryCyclicIntersectionOccurrenceSet R z a b) := by
  let V := {p : EuclideanSpace ℝ (Fin 2) // p ∈ R.vertices}
  let A0 : V → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun p => openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ z a
  let A1 : V → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun p => openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ a b
  let A2 : V → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun p => openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ b z
  let Occ := TriangleBoundaryCyclicIntersectionOccurrenceSet R z a b
  rcases hgp with ⟨_, _, _, _, _, _, _, _, _, _, hboundary⟩
  have hsegmentCarrier :
      ∀ p : V, segment ℝ p.1 (R.successor p).1 ⊆ J.carrier := by
    intro p x hx
    rw [R.cyclic_carrier_eq]
    exact Set.mem_iUnion.2 ⟨p, hx⟩
  have hA0fin : ∀ p : V, (A0 p).Finite := by
    intro p
    refine hboundary.subset ?_
    intro x hx
    exact ⟨hsegmentCarrier p ((openSegment_subset_segment ℝ p.1 (R.successor p).1) hx.1),
      Or.inl (Or.inl ((openSegment_subset_segment ℝ z a) hx.2))⟩
  have hA1fin : ∀ p : V, (A1 p).Finite := by
    intro p
    refine hboundary.subset ?_
    intro x hx
    exact ⟨hsegmentCarrier p ((openSegment_subset_segment ℝ p.1 (R.successor p).1) hx.1),
      Or.inl (Or.inr ((openSegment_subset_segment ℝ a b) hx.2))⟩
  have hA2fin : ∀ p : V, (A2 p).Finite := by
    intro p
    refine hboundary.subset ?_
    intro x hx
    exact ⟨hsegmentCarrier p ((openSegment_subset_segment ℝ p.1 (R.successor p).1) hx.1),
      Or.inr ((openSegment_subset_segment ℝ b z) hx.2)⟩
  have : ∀ p : V, Fintype (A0 p) := fun p => (hA0fin p).fintype
  have : ∀ p : V, Fintype (A1 p) := fun p => (hA1fin p).fintype
  have : ∀ p : V, Fintype (A2 p) := fun p => (hA2fin p).fintype
  let TaggedFiber : V → Type :=
    fun p => (A0 p) ⊕ ((A1 p) ⊕ (A2 p))
  let encode : (Sigma TaggedFiber) → V × Fin 3 × EuclideanSpace ℝ (Fin 2) :=
    fun y =>
      match y.2 with
      | Sum.inl x => (y.1, (0 : Fin 3), x.1)
      | Sum.inr (Sum.inl x) => (y.1, (1 : Fin 3), x.1)
      | Sum.inr (Sum.inr x) => (y.1, (2 : Fin 3), x.1)
  have hCongr :
      (Set.univ : Set (Sigma TaggedFiber)).ncard = Occ.ncard := by
    refine Set.ncard_congr (s := (Set.univ : Set (Sigma TaggedFiber))) (t := Occ)
      (fun y _ => encode y) ?_ ?_ ?_
    · intro y hy
      rcases y with ⟨p, x | x | x⟩
      · rcases x with ⟨x, hx⟩
        change x ∈ openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ z a at hx
        dsimp [Occ, encode, TriangleBoundaryCyclicIntersectionOccurrenceSet]
        exact ⟨hx.1, Or.inl ⟨rfl, hx.2⟩⟩
      · rcases x with ⟨x, hx⟩
        change x ∈ openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ a b at hx
        dsimp [Occ, encode, TriangleBoundaryCyclicIntersectionOccurrenceSet]
        exact ⟨hx.1, Or.inr (Or.inl ⟨rfl, hx.2⟩)⟩
      · rcases x with ⟨x, hx⟩
        change x ∈ openSegment ℝ p.1 (R.successor p).1 ∩ openSegment ℝ b z at hx
        dsimp [Occ, encode, TriangleBoundaryCyclicIntersectionOccurrenceSet]
        exact ⟨hx.1, Or.inr (Or.inr ⟨rfl, hx.2⟩)⟩
    · intro y₁ y₂ hy₁ hy₂ henc
      rcases y₁ with ⟨p₁, x₁ | x₁ | x₁⟩
      · rcases y₂ with ⟨p₂, x₂ | x₂ | x₂⟩
        · cases x₁
          cases x₂
          simp only [Sigma.mk.injEq] at henc ⊢
          rcases henc with ⟨rfl, rfl⟩
          simp
        · simp [encode, TaggedFiber] at henc
        · simp [encode, TaggedFiber] at henc
      · rcases y₂ with ⟨p₂, x₂ | x₂ | x₂⟩
        · simp [encode, TaggedFiber] at henc
        · cases x₁
          cases x₂
          simp only [Sigma.mk.injEq] at henc ⊢
          rcases henc with ⟨rfl, rfl⟩
          simp
        · simp [encode, TaggedFiber] at henc
      · rcases y₂ with ⟨p₂, x₂ | x₂ | x₂⟩
        · simp [encode, TaggedFiber] at henc
        · simp [encode, TaggedFiber] at henc
        · cases x₁
          cases x₂
          simp only [Sigma.mk.injEq] at henc ⊢
          rcases henc with ⟨rfl, rfl⟩
          simp
    · intro q hq
      rcases q with ⟨p, i, x⟩
      change x ∈ openSegment ℝ p.1 (R.successor p).1 ∧
        ((i = (0 : Fin 3) ∧ x ∈ openSegment ℝ z a) ∨
          (i = (1 : Fin 3) ∧ x ∈ openSegment ℝ a b) ∨
            (i = (2 : Fin 3) ∧ x ∈ openSegment ℝ b z)) at hq
      rcases hq with ⟨hpseg, (⟨hi, hx⟩ | ⟨hi, hx⟩ | ⟨hi, hx⟩)⟩
      · subst i
        refine ⟨⟨p, Sum.inl ⟨x, ?_⟩⟩, by simp, ?_⟩
        · exact ⟨hpseg, hx⟩
        · simp [encode, TaggedFiber]
      · subst i
        refine ⟨⟨p, Sum.inr (Sum.inl ⟨x, ?_⟩)⟩, by simp, ?_⟩
        · exact ⟨hpseg, hx⟩
        · simp [encode, TaggedFiber]
      · subst i
        refine ⟨⟨p, Sum.inr (Sum.inr ⟨x, ?_⟩)⟩, by simp, ?_⟩
        · exact ⟨hpseg, hx⟩
        · simp [encode, TaggedFiber]
  have hOccCard :
      Occ.ncard = Nat.card (Sigma TaggedFiber) := by
    rw [Set.ncard_univ] at hCongr
    exact hCongr.symm
  have hSigma :
      Nat.card (Sigma TaggedFiber) =
        ∑ p : V, ((A0 p).ncard + (A1 p).ncard + (A2 p).ncard) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Fintype.card_sum, Fintype.card_sum]
    have h0 : Fintype.card (A0 p) = (A0 p).ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq (A0 p)
    have h1 : Fintype.card (A1 p) = (A1 p).ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq (A1 p)
    have h2 : Fintype.card (A2 p) = (A2 p).ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq (A2 p)
    rw [h0, h1, h2]
    ac_rfl
  have hOccSum :
      Occ.ncard = ∑ p : V, ((A0 p).ncard + (A1 p).ncard + (A2 p).ncard) :=
    hOccCard.trans hSigma
  rw [TriangleBoundaryCyclicIntersectionMultiplicity]
  change R.vertices.attach.sum
      (fun p : V => (A0 p).ncard + (A1 p).ncard + (A2 p).ncard) = Occ.ncard
  rw [Finset.attach_eq_univ]
  exact hOccSum.symm
