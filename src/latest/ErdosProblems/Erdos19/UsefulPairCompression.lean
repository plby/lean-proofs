import ErdosProblems.Erdos19.PairCompression

/-!
# Pair-compression strengthening of the projective-scale argument

The arithmetic and incidence estimates are reused from `Core`; these proofs
retain the disjoint-pair witnesses through every coloring branch.
-/

namespace Erdos19.SetHypergraph

variable {X : Type*}

theorem pairCompressible_of_useful_pairs [Fintype X] (H : SetHypergraph X)
    {n t : ℕ} (hn : 2 ≤ n) (left right : Fin t → H)
    (hendpoints : Function.Injective (Sum.elim left right))
    (hall_intersect : ∀ (a b : Fin t ⊕ Fin t), a ≠ b →
      ((Sum.elim left right a).1 ∩ (Sum.elim left right b).1).Nonempty)
    (huseful : ∀ i, H.IsUseful n (left i) (right i))
    (hcard : Fintype.card H = n + t) :
    H.PairCompressible n := by
  classical
  let endpoint : Fin t ⊕ Fin t → H := Sum.elim left right
  have endpoint_injective : Function.Injective endpoint := hendpoints
  let forbidden (i : Fin t) : Set H :=
    H.commonNeighborEdges (left i) (right i) ∪ ({left i, right i} : Set H)
  let candidate (i : Fin t) : Finset H := (forbidden i)ᶜ.toFinset
  have hforbidden (i : Fin t) : (forbidden i).ncard ≤ n := by
    calc
      (forbidden i).ncard ≤
          (H.commonNeighborEdges (left i) (right i)).ncard +
            ({left i, right i} : Set H).ncard := Set.ncard_union_le _ _
      _ = (H.commonNeighborEdges (left i) (right i)).ncard + 2 := by
        rw [Set.ncard_pair (huseful i).1]
      _ ≤ (n - 2) + 2 := Nat.add_le_add_right (huseful i).2.2 2
      _ = n := by omega
  have hcandidate (i : Fin t) : t ≤ (candidate i).card := by
    rw [← Set.ncard_eq_toFinset_card']
    change t ≤ (forbidden i)ᶜ.ncard
    rw [Set.ncard_compl, Nat.card_eq_fintype_card, hcard]
    have hi := hforbidden i
    omega
  obtain ⟨z, z_injective, hz⟩ :=
    exists_injective_mem_of_card_le candidate (by simpa using hcandidate)
  have hz_not_forbidden (i : Fin t) : z i ∉ forbidden i := by
    simpa [candidate] using hz i
  have hz_ne_left (i : Fin t) : z i ≠ left i := by
    intro h
    apply hz_not_forbidden i
    exact Or.inr (by simp [h])
  have hz_ne_right (i : Fin t) : z i ≠ right i := by
    intro h
    apply hz_not_forbidden i
    exact Or.inr (by simp [h])
  have hz_ne_endpoint (i : Fin t) (a : Fin t ⊕ Fin t) : z i ≠ endpoint a := by
    intro hza
    by_cases hal : a = Sum.inl i
    · subst a
      exact hz_ne_left i (by simpa [endpoint] using hza)
    by_cases har : a = Sum.inr i
    · subst a
      exact hz_ne_right i (by simpa [endpoint] using hza)
    have hal' : a ≠ Sum.inl i := hal
    have har' : a ≠ Sum.inr i := har
    have hmeet_left : (endpoint a).1 ∩ (left i).1 |>.Nonempty := by
      simpa [endpoint] using hall_intersect a (Sum.inl i) hal'
    have hmeet_right : (endpoint a).1 ∩ (right i).1 |>.Nonempty := by
      simpa [endpoint] using hall_intersect a (Sum.inr i) har'
    have ha_ne_left : endpoint a ≠ left i := by
      intro ha
      apply hal'
      apply endpoint_injective
      simpa [endpoint] using ha
    have ha_ne_right : endpoint a ≠ right i := by
      intro ha
      apply har'
      apply endpoint_injective
      simpa [endpoint] using ha
    have ha_common : endpoint a ∈ H.commonNeighborEdges (left i) (right i) := by
      constructor
      · exact ⟨ha_ne_left.symm, by simpa [Set.inter_comm] using hmeet_left⟩
      · exact ⟨ha_ne_right.symm, by simpa [Set.inter_comm] using hmeet_right⟩
    apply hz_not_forbidden i
    left
    simpa [hza] using ha_common
  have hsome_disjoint (i : Fin t) :
      Disjoint (left i).1 (z i).1 ∨ Disjoint (right i).1 (z i).1 := by
    by_cases hl : Disjoint (left i).1 (z i).1
    · exact Or.inl hl
    right
    by_contra hr
    have hz_common : z i ∈ H.commonNeighborEdges (left i) (right i) := by
      constructor
      · exact ⟨(hz_ne_left i).symm,
          Set.not_disjoint_iff_nonempty_inter.mp hl⟩
      · exact ⟨(hz_ne_right i).symm,
          Set.not_disjoint_iff_nonempty_inter.mp hr⟩
    exact hz_not_forbidden i (Or.inl hz_common)
  let chooseLeft (i : Fin t) : Prop := Disjoint (left i).1 (z i).1
  let chosen (i : Fin t) : H := if chooseLeft i then left i else right i
  let side (i : Fin t) : Fin t ⊕ Fin t :=
    if chooseLeft i then Sum.inl i else Sum.inr i
  have chosen_eq_endpoint (i : Fin t) : chosen i = endpoint (side i) := by
    simp only [chosen, side, endpoint, chooseLeft]
    split <;> rfl
  let pairIndex : Fin t ⊕ Fin t → Fin t := Sum.elim id id
  have pairIndex_side (i : Fin t) : pairIndex (side i) = i := by
    simp only [pairIndex, side]
    split <;> rfl
  have side_injective : Function.Injective side := by
    intro i j hij
    simpa only [pairIndex_side] using congrArg pairIndex hij
  have chosen_injective : Function.Injective chosen := by
    intro i j hij
    apply side_injective
    apply endpoint_injective
    simpa only [← chosen_eq_endpoint] using hij
  have hchosen_disjoint (i : Fin t) : Disjoint (chosen i).1 (z i).1 := by
    by_cases hl : chooseLeft i
    · simpa [chosen, hl, chooseLeft] using hl
    · simpa [chosen, hl] using (hsome_disjoint i).resolve_left hl
  have hchosen_z_injective : Function.Injective (Sum.elim chosen z) := by
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · exact congrArg Sum.inl (chosen_injective hab)
    · exfalso
      exact hz_ne_endpoint j (side i) (by
        rw [← chosen_eq_endpoint]
        exact hab.symm)
    · exfalso
      exact hz_ne_endpoint i (side j) (by
        rw [← chosen_eq_endpoint]
        exact hab)
    · exact congrArg Sum.inr (z_injective hab)
  apply H.pairCompressible_of_disjoint_pairs chosen z hchosen_z_injective
    hchosen_disjoint
  omega

theorem pairCompressible_of_useful_partition [Fintype X]
    (H : SetHypergraph X) {n : ℕ} (hn : 2 ≤ n) (A B : Set H)
    (hdisjoint : Disjoint A B) (hpartition : A ∪ B = Set.univ)
    (hsurplus : A.ncard + B.ncard - n ≤ A.ncard / 4)
    (huseful : ∀ {e : H}, e ∈ A → ∀ {f : H}, f ∈ A →
      e ≠ f → (e.1 ∩ f.1).Nonempty → H.IsUseful n e f) :
    H.PairCompressible n := by
  classical
  have hpartition_card : Fintype.card H = A.ncard + B.ncard := by
    calc
      Fintype.card H = (Set.univ : Set H).ncard := by simp
      _ = (A ∪ B).ncard := by rw [hpartition]
      _ = A.ncard + B.ncard := Set.ncard_union_eq hdisjoint
  by_cases hsmall : Fintype.card H ≤ n
  · exact H.pairCompressible_of_card_le hsmall
  let t := A.ncard + B.ncard - n
  obtain ⟨M, hM, hmax⟩ := H.exists_maximum_disjointnessMatching
  by_cases hlargeMatching : t ≤ M.edgeSet.ncard
  · apply H.pairCompressible_of_disjointnessMatching M hM
    rw [hpartition_card]
    dsimp only [t] at hlargeMatching
    omega
  have hMt : M.edgeSet.ncard < t := Nat.lt_of_not_ge hlargeMatching
  have hA_four : 4 * t ≤ A.ncard := by
    dsimp only [t]
    omega
  let S : Set H := A \ M.verts
  have hS : 2 * t ≤ S.ncard := by
    have hdiff := Set.le_ncard_sdiff M.verts A
    change A.ncard - M.verts.ncard ≤ S.ncard at hdiff
    rw [H.matching_verts_ncard M hM] at hdiff
    omega
  have hindex_card :
      Fintype.card (Fin t ⊕ Fin t) ≤ Fintype.card S := by
    rw [Fintype.card_sum, Set.fintypeCard_eq_ncard]
    simpa [two_mul] using hS
  obtain ⟨select : (Fin t ⊕ Fin t) ↪ S⟩ :=
    Function.Embedding.nonempty_of_card_le hindex_card
  let selected : Fin t ⊕ Fin t → H := fun a ↦ (select a).1
  let left : Fin t → H := fun i ↦ selected (Sum.inl i)
  let right : Fin t → H := fun i ↦ selected (Sum.inr i)
  have elim_eq_selected (a : Fin t ⊕ Fin t) :
      Sum.elim left right a = selected a := by
    rcases a with i | i <;> rfl
  have hselected : Function.Injective (Sum.elim left right) := by
    intro a b hab
    apply select.injective
    apply Subtype.ext
    rw [elim_eq_selected a, elim_eq_selected b] at hab
    exact hab
  have selected_mem_A (a : Fin t ⊕ Fin t) : selected a ∈ A :=
    (select a).2.1
  have selected_not_mem_M (a : Fin t ⊕ Fin t) : selected a ∉ M.verts :=
    (select a).2.2
  have hunmatched_pairwise :=
    H.maximum_disjointnessMatching_unmatched_pairwise_intersect M hM hmax
  have hall_intersect : ∀ (a b : Fin t ⊕ Fin t), a ≠ b →
      ((Sum.elim left right a).1 ∩
        (Sum.elim left right b).1).Nonempty := by
    intro a b hab
    have hne : selected a ≠ selected b := by
      intro h
      apply hab
      exact select.injective (Subtype.ext h)
    have hinter := hunmatched_pairwise (selected_not_mem_M a)
      (selected_not_mem_M b) hne
    rw [elim_eq_selected a, elim_eq_selected b]
    exact hinter
  have hpairs_useful : ∀ i, H.IsUseful n (left i) (right i) := by
    intro i
    apply huseful (selected_mem_A (Sum.inl i))
      (selected_mem_A (Sum.inr i))
    · intro h
      exact Sum.inl_ne_inr (select.injective (Subtype.ext h))
    · exact hall_intersect (Sum.inl i) (Sum.inr i) Sum.inl_ne_inr
  apply H.pairCompressible_of_useful_pairs hn left right hselected
    hall_intersect hpairs_useful
  rw [hpartition_card]
  dsimp only [t]
  omega

theorem pairCompressible_of_pairwise_intersecting_outside_density [Fintype X]
    (H : SetHypergraph X) {n t q : ℕ} (hn : 2 ≤ n) (S : Set H)
    (bad : Set X) (hcard : Fintype.card H = n + t)
    (hpairwise : S.Pairwise fun e f ↦ (e.1 ∩ f.1).Nonempty)
    (houtside : ∀ e ∈ S, q ≤ (e.1 \ bad).ncard)
    (hdensity : Fintype.card X < (S.ncard - 2 * (t - 1)) * q)
    (hgood : ∀ (e f : H), e ∈ S → f ∈ S → e ≠ f →
      ∀ x, x ∉ bad → x ∈ e.1 → x ∈ f.1 → H.IsUseful n e f) :
    H.PairCompressible n := by
  obtain ⟨left, right, hinjective, huseful, hmem⟩ :=
    H.exists_useful_pairs_of_outside_density n S t q bad
      houtside hdensity hgood
  have endpoint_mem (a : Fin t ⊕ Fin t) : Sum.elim left right a ∈ S := by
    rcases a with i | i
    · exact (hmem i).1
    · exact (hmem i).2
  have hall_intersect : ∀ (a b : Fin t ⊕ Fin t), a ≠ b →
      ((Sum.elim left right a).1 ∩
        (Sum.elim left right b).1).Nonempty := by
    intro a b hab
    apply hpairwise (endpoint_mem a) (endpoint_mem b)
    intro heq
    exact hab (hinjective heq)
  exact H.pairCompressible_of_useful_pairs hn left right hinjective
    hall_intersect huseful hcard

theorem pairCompressible_of_projectiveScale_outside_density [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall t qOutside : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 1 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (S : Set H) (hcard : Fintype.card H = n + t)
    (hscale : ∀ e ∈ S, e.1.ncard = projectiveScale n)
    (hpairwise : S.Pairwise fun e f ↦ (e.1 ∩ f.1).Nonempty)
    (houtside : ∀ e ∈ S, qOutside ≤
      (e.1 \ {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}).ncard)
    (hdensity : n < (S.ncard - 2 * (t - 1)) * qOutside) :
    H.PairCompressible n := by
  let bad : Set X :=
    {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}
  apply H.pairCompressible_of_pairwise_intersecting_outside_density (by omega) S bad
    hcard hpairwise
  · simpa only [bad] using houtside
  · simpa only [hvertices] using hdensity
  · intro e f he hf hef x hxbad hxe hxf
    have hsmallx :
        (H.smallIncidentEdges x (projectiveScale n)).ncard ≤ qSmall := by
      change ¬qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard at hxbad
      omega
    exact H.isUseful_of_few_small_incident_below_projectiveScale hlinear
      n r qSmall hn hvertices hr hrscale hmin hdefect e f hef x hxe hxf
      (hscale e he) (hscale f hf) hsmallx

theorem pairCompressible_of_projectiveScale_claim [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall s qOutside t : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 1 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hcard : Fintype.card H = n + t)
    (houtside : qOutside + s ≤ projectiveScale n + 1)
    (hdensity : n <
      (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
          ({e : H | e.1.ncard = projectiveScale n ∧
            s ≤ (e.1 ∩
              {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}).ncard} :
            Set H).ncard -
          4 * (t - 1)) * qOutside) :
    H.PairCompressible n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let bad : Set X :=
    {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}
  let Aplus : Set H := {e | e.1.ncard = projectiveScale n}
  let heavy : Set H :=
    {e | e.1.ncard = projectiveScale n ∧ s ≤ (e.1 ∩ bad).ncard}
  obtain ⟨M, hM, hmax⟩ := H.exists_maximum_disjointnessMatching
  by_cases hlarge : t ≤ M.edgeSet.ncard
  · apply H.pairCompressible_of_disjointnessMatching M hM
    rw [hcard]
    omega
  have hMlt : M.edgeSet.ncard < t := Nat.lt_of_not_ge hlarge
  have hMle : M.edgeSet.ncard ≤ t - 1 := by omega
  let S : Set H := Aplus \ (heavy ∪ M.verts)
  have hSscale : ∀ e ∈ S, e.1.ncard = projectiveScale n := by
    intro e he
    exact he.1
  have hSpairwise : S.Pairwise fun e f ↦ (e.1 ∩ f.1).Nonempty := by
    intro e he f hf hef
    apply H.maximum_disjointnessMatching_unmatched_pairwise_intersect M hM hmax
    · intro heM
      exact he.2 (Or.inr heM)
    · intro hfM
      exact hf.2 (Or.inr hfM)
    · exact hef
  have hunion : (heavy ∪ M.verts).ncard ≤ heavy.ncard + M.verts.ncard :=
    Set.ncard_union_le _ _
  have hdiff := Set.le_ncard_sdiff (heavy ∪ M.verts) Aplus
  have hbase : Aplus.ncard - heavy.ncard - M.verts.ncard ≤ S.ncard := by
    calc
      Aplus.ncard - heavy.ncard - M.verts.ncard =
          Aplus.ncard - (heavy.ncard + M.verts.ncard) := Nat.sub_sub _ _ _
      _ ≤ Aplus.ncard - (heavy ∪ M.verts).ncard :=
        Nat.sub_le_sub_left hunion _
      _ ≤ S.ncard := hdiff
  have hverts := H.matching_verts_ncard M hM
  have hSbound :
      Aplus.ncard - heavy.ncard - 2 * (t - 1) ≤ S.ncard := by
    calc
      Aplus.ncard - heavy.ncard - 2 * (t - 1) ≤
          Aplus.ncard - heavy.ncard - M.verts.ncard := by
        rw [hverts]
        omega
      _ ≤ S.ncard := hbase
  have hSresidual :
      Aplus.ncard - heavy.ncard - 4 * (t - 1) ≤
        S.ncard - 2 * (t - 1) := by
    have h := Nat.sub_le_sub_right hSbound (2 * (t - 1))
    omega
  have hSdensity : n < (S.ncard - 2 * (t - 1)) * qOutside := by
    have hdensity' : n <
        (Aplus.ncard - heavy.ncard - 4 * (t - 1)) * qOutside := by
      simpa only [Aplus, heavy, bad] using hdensity
    exact hdensity'.trans_le (Nat.mul_le_mul_right qOutside hSresidual)
  have hSoutside : ∀ e ∈ S, qOutside ≤ (e.1 \ bad).ncard := by
    intro e he
    have heplus : e ∈ Aplus := he.1
    have henotheavy : e ∉ heavy := by
      intro heheavy
      exact he.2 (Or.inl heheavy)
    have hinter : (e.1 ∩ bad).ncard < s := by
      by_contra hnot
      apply henotheavy
      exact ⟨heplus, by omega⟩
    exact ncard_sdiff_ge_of_ncard_inter_lt e.1 bad (projectiveScale n)
      s qOutside heplus hinter houtside
  apply H.pairCompressible_of_projectiveScale_outside_density hlinear
    n r qSmall t qOutside hn hvertices hr hrscale hmin hdefect S hcard
    hSscale hSpairwise
  · simpa only [bad] using hSoutside
  · simpa only [hvertices] using hSdensity

theorem pairCompressible_of_projectiveScale_claim_of_floor_density [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall s qOutside t : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 1 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hcard : Fintype.card H = n + t)
    (hs : 0 < s)
    (houtside : qOutside + s ≤ projectiveScale n + 1)
    (hdensity : n <
      (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
          ((({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
                (projectiveScale n - 1) / (qSmall + 1)) *
              ((n - 1) / (projectiveScale n - 1)) / s) -
          4 * (t - 1)) * qOutside) :
    H.PairCompressible n := by
  classical
  let Aminus : Set H := {e | e.1.ncard < projectiveScale n}
  let bad : Set X :=
    {x | qSmall < (H.smallIncidentEdges x (projectiveScale n)).ncard}
  let heavy : Set H :=
    {e | e.1.ncard = projectiveScale n ∧ s ≤ (e.1 ∩ bad).ncard}
  let badBound : ℕ := Aminus.ncard * (projectiveScale n - 1) / (qSmall + 1)
  let heavyBound : ℕ :=
    badBound * ((n - 1) / (projectiveScale n - 1)) / s
  have hbadmul : bad.ncard * (qSmall + 1) ≤
      Aminus.ncard * (projectiveScale n - 1) := by
    have h := H.badVertices_ncard_mul_le_subscaleEdges
      (projectiveScale n) (qSmall + 1)
    simpa only [Aminus, bad, Nat.lt_iff_add_one_le] using h
  have hbad : bad.ncard ≤ badBound := by
    dsimp only [badBound]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < qSmall + 1)).2 hbadmul
  have hk : 2 ≤ projectiveScale n := two_le_projectiveScale hn
  have hheavymul : heavy.ncard * s ≤
      bad.ncard * ((n - 1) / (projectiveScale n - 1)) := by
    have h := H.heavyProjectiveEdges_ncard_mul_le_badVertices hlinear
      (projectiveScale n) s hk bad
    simpa only [heavy, hvertices] using h
  have hheavymul' : heavy.ncard * s ≤
      badBound * ((n - 1) / (projectiveScale n - 1)) :=
    hheavymul.trans (Nat.mul_le_mul_right _ hbad)
  have hheavy : heavy.ncard ≤ heavyBound := by
    dsimp only [heavyBound]
    exact (Nat.le_div_iff_mul_le hs).2 hheavymul'
  apply H.pairCompressible_of_projectiveScale_claim hlinear
    n r qSmall s qOutside t hn hvertices hr hrscale hmin hdefect hcard
    houtside
  have hdensity' : n <
      (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
          heavyBound - 4 * (t - 1)) * qOutside := by
    simpa only [Aminus, badBound, heavyBound] using hdensity
  have hresidual :
      ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
            heavyBound - 4 * (t - 1) ≤
        ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
            heavy.ncard - 4 * (t - 1) := by
    exact Nat.sub_le_sub_right
      (Nat.sub_le_sub_left hheavy
        ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard)
      (4 * (t - 1))
  have := hdensity'.trans_le (Nat.mul_le_mul_right qOutside hresidual)
  simpa only [heavy, bad] using this

end Erdos19.SetHypergraph

#print axioms Erdos19.SetHypergraph.pairCompressible_of_useful_pairs
#print axioms Erdos19.SetHypergraph.pairCompressible_of_useful_partition
#print axioms Erdos19.SetHypergraph.pairCompressible_of_pairwise_intersecting_outside_density
#print axioms Erdos19.SetHypergraph.pairCompressible_of_projectiveScale_outside_density
#print axioms Erdos19.SetHypergraph.pairCompressible_of_projectiveScale_claim
#print axioms Erdos19.SetHypergraph.pairCompressible_of_projectiveScale_claim_of_floor_density
