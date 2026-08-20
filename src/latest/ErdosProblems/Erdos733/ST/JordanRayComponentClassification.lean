import ErdosProblems.Erdos733.ST.JordanLocalSideData
import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.JordanLocalSideDistinctComponents
import ErdosProblems.Erdos733.ST.JordanGenericRayReachesLocalSide
import ErdosProblems.Erdos733.ST.JordanExteriorLocalSideUnbounded
import ErdosProblems.Erdos733.ST.JordanUnboundedComplementComponentUnique

open Classical
noncomputable section

-- [TABLET NODE: JordanRayComponentClassification]
lemma JordanRayComponentClassification
    (J : SimpleClosedPolygonalCurve) (S : JordanLocalSideData J) :
    ∃ boundedComponent unboundedComponent : Set (EuclideanSpace ℝ (Fin 2)),
      ComplementComponent J.carrier boundedComponent ∧
        ComplementComponent J.carrier unboundedComponent ∧
          boundedComponent ≠ unboundedComponent ∧
            ((S.leftRegion ⊆ boundedComponent ∧
                S.rightRegion ⊆ unboundedComponent) ∨
              (S.leftRegion ⊆ unboundedComponent ∧
                S.rightRegion ⊆ boundedComponent)) ∧
              (∀ F : Set (EuclideanSpace ℝ (Fin 2)),
                ComplementComponent J.carrier F →
                  F = boundedComponent ∨ F = unboundedComponent) ∧
                (∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ J.carrierᶜ →
                    p ∈ boundedComponent ∨ p ∈ unboundedComponent) ∧
                  Bornology.IsBounded boundedComponent ∧
                    ¬ Bornology.IsBounded unboundedComponent := by
-- BODY
  obtain ⟨C_L, C_R, hC_L, hC_R, hC_ne, hleft, hright⟩ :=
    JordanLocalSideDistinctComponents J S
  have point_classification :
      ∀ p : EuclideanSpace ℝ (Fin 2),
        p ∈ J.carrierᶜ → p ∈ C_L ∨ p ∈ C_R := by
    intro p hp
    obtain ⟨A, hAne, hAsub, hAconn, hpA, hAside⟩ :=
      JordanGenericRayReachesLocalSide J S p hp
    rcases hAside with hAleft | hAright
    · left
      have hAinter : (A ∩ C_L).Nonempty := by
        rcases hAleft with ⟨a, haA, haleft⟩
        exact ⟨a, haA, hleft haleft⟩
      have hAunion : A ∪ C_L ⊆ C_L :=
        hC_L.2.2.2 (A ∪ C_L)
          (hAne.mono Set.subset_union_left)
          (Set.union_subset hAsub hC_L.2.1)
          (IsConnected.union hAinter hAconn hC_L.2.2.1)
          Set.subset_union_right
      exact hAunion (Set.mem_union_left C_L hpA)
    · right
      have hAinter : (A ∩ C_R).Nonempty := by
        rcases hAright with ⟨a, haA, haright⟩
        exact ⟨a, haA, hright haright⟩
      have hAunion : A ∪ C_R ⊆ C_R :=
        hC_R.2.2.2 (A ∪ C_R)
          (hAne.mono Set.subset_union_left)
          (Set.union_subset hAsub hC_R.2.1)
          (IsConnected.union hAinter hAconn hC_R.2.2.1)
          Set.subset_union_right
      exact hAunion (Set.mem_union_left C_R hpA)
  have component_classification :
      ∀ F : Set (EuclideanSpace ℝ (Fin 2)),
        ComplementComponent J.carrier F → F = C_L ∨ F = C_R := by
    intro F hF
    rcases hF.1 with ⟨p, hpF⟩
    rcases point_classification p (hF.2.1 hpF) with hpL | hpR
    · left
      have hinter : (F ∩ C_L).Nonempty := ⟨p, hpF, hpL⟩
      have hunion : IsConnected (F ∪ C_L) :=
        IsConnected.union hinter hF.2.2.1 hC_L.2.2.1
      apply Set.Subset.antisymm
      · exact Set.subset_union_left.trans
          (hC_L.2.2.2 (F ∪ C_L)
            (hF.1.mono Set.subset_union_left)
            (Set.union_subset hF.2.1 hC_L.2.1) hunion
            Set.subset_union_right)
      · exact Set.subset_union_right.trans
          (hF.2.2.2 (F ∪ C_L)
            (hF.1.mono Set.subset_union_left)
            (Set.union_subset hF.2.1 hC_L.2.1) hunion
            Set.subset_union_left)
    · right
      have hinter : (F ∩ C_R).Nonempty := ⟨p, hpF, hpR⟩
      have hunion : IsConnected (F ∪ C_R) :=
        IsConnected.union hinter hF.2.2.1 hC_R.2.2.1
      apply Set.Subset.antisymm
      · exact Set.subset_union_left.trans
          (hC_R.2.2.2 (F ∪ C_R)
            (hF.1.mono Set.subset_union_left)
            (Set.union_subset hF.2.1 hC_R.2.1) hunion
            Set.subset_union_right)
      · exact Set.subset_union_right.trans
          (hF.2.2.2 (F ∪ C_R)
            (hF.1.mono Set.subset_union_left)
            (Set.union_subset hF.2.1 hC_R.2.1) hunion
            Set.subset_union_left)
  obtain ⟨T, hTne, hTsub, hTconn, hTunbounded, hTside⟩ :=
    JordanExteriorLocalSideUnbounded J S
  have one_unbounded :
      ¬ Bornology.IsBounded C_L ∨ ¬ Bornology.IsBounded C_R := by
    rcases hTside with hTleft | hTright
    · left
      have hTinter : (T ∩ C_L).Nonempty := by
        rcases hTleft with ⟨a, haT, haleft⟩
        exact ⟨a, haT, hleft haleft⟩
      have hTunion : T ∪ C_L ⊆ C_L :=
        hC_L.2.2.2 (T ∪ C_L)
          (hTne.mono Set.subset_union_left)
          (Set.union_subset hTsub hC_L.2.1)
          (IsConnected.union hTinter hTconn hC_L.2.2.1)
          Set.subset_union_right
      intro hCLbounded
      apply hTunbounded
      exact hCLbounded.subset
        (Set.subset_union_left.trans hTunion)
    · right
      have hTinter : (T ∩ C_R).Nonempty := by
        rcases hTright with ⟨a, haT, haright⟩
        exact ⟨a, haT, hright haright⟩
      have hTunion : T ∪ C_R ⊆ C_R :=
        hC_R.2.2.2 (T ∪ C_R)
          (hTne.mono Set.subset_union_left)
          (Set.union_subset hTsub hC_R.2.1)
          (IsConnected.union hTinter hTconn hC_R.2.2.1)
          Set.subset_union_right
      intro hCRbounded
      apply hTunbounded
      exact hCRbounded.subset
        (Set.subset_union_left.trans hTunion)
  have not_both_unbounded :
      ¬ (¬ Bornology.IsBounded C_L ∧ ¬ Bornology.IsBounded C_R) := by
    rintro ⟨hCLunbounded, hCRunbounded⟩
    apply hC_ne
    exact JordanUnboundedComplementComponentUnique J C_L C_R
      hC_L hC_R hCLunbounded hCRunbounded
  rcases one_unbounded with hCLunbounded | hCRunbounded
  · have hCRbounded : Bornology.IsBounded C_R := by
      by_contra hCRunbounded
      exact not_both_unbounded ⟨hCLunbounded, hCRunbounded⟩
    refine ⟨C_R, C_L, hC_R, hC_L, hC_ne.symm, Or.inr ⟨hleft, hright⟩,
      ?_, ?_, hCRbounded, hCLunbounded⟩
    · intro F hF
      rcases component_classification F hF with hFL | hFR
      · exact Or.inr hFL
      · exact Or.inl hFR
    · intro p hp
      rcases point_classification p hp with hpL | hpR
      · exact Or.inr hpL
      · exact Or.inl hpR
  · have hCLbounded : Bornology.IsBounded C_L := by
      by_contra hCLunbounded
      exact not_both_unbounded ⟨hCLunbounded, hCRunbounded⟩
    exact ⟨C_L, C_R, hC_L, hC_R, hC_ne, Or.inl ⟨hleft, hright⟩,
      component_classification, point_classification, hCLbounded, hCRunbounded⟩
