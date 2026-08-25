import StackExchange.Puzzling139335.JordanInvolution

/-!
# The longer arc between non-antipodal boundary points

A fixed-point-free involution of a Jordan curve swaps the two arcs between
a point and its image.  Splitting one of those arcs at a third point gives
the precise three-arc decomposition used by the variation argument.
-/

open Set Schoenflies

namespace Schoenflies

/-- A free involution swaps the two arcs joining a point to its image. -/
theorem IsCutPair.image_fst_eq_snd_of_free_involution {C A B : Set Plane} {p : Plane}
    (e : Plane ≃ₜ Plane) (h : IsCutPair C p (e p) A B)
    (he : e '' C = C) (hinv : Function.Involutive e)
    (hfree : ∀ x ∈ C, e x ≠ x) : e '' A = B := by
  have harc : IsArcBetween (e '' A) p (e p) := by
    simpa only [hinv p] using (h.fst.image_homeomorph e).reverse
  have hsub : e '' A ⊆ C := by
    rw [← he]
    exact image_mono h.fst_subset
  rcases h.arc_eq_fst_or_snd harc hsub with hAA | hAB
  · have hmaps : MapsTo e A A := by
      intro x hx
      rw [← hAA]
      exact mem_image_of_mem e hx
    obtain ⟨x, hx, hfix⟩ :=
      h.fst.exists_fixedPoint_of_continuousOn e.continuous.continuousOn hmaps
    exact False.elim (hfree x (h.fst_subset hx) hfix)
  · exact hAB

end Schoenflies

namespace Puzzling139335

/-- The long arc is the image of the short arc with two congruent, nontrivial
bridges attached at its ends.  The meeting conditions state the order exactly. -/
def HasAntipodalBridge (e : Plane ≃ₜ Plane) (S L : Set Plane) (p q : Plane) : Prop :=
  ∃ K : Set Plane, IsArcBetween K q (e p) ∧
    L = (K ∪ e '' S) ∪ e '' K ∧
    (∀ z ∈ K, z ∈ e '' S → z = e p) ∧
    (∀ z ∈ K ∪ e '' S, z ∈ e '' K → z = e q)

private theorem bridge_from_split {C J J' S K : Set Plane} {p q : Plane}
    (e : Plane ≃ₜ Plane) (hinv : Function.Involutive e)
    (hJ : IsCutPair C p (e p) J J') (heJ : e '' J = J')
    (hS : IsArcBetween S p q) (hK : IsArcBetween K q (e p))
    (hunion : S ∪ K = J) (hinter : S ∩ K = {q}) :
    IsCutPair C p q S ((K ∪ e '' S) ∪ e '' K) ∧
      HasAntipodalBridge e S ((K ∪ e '' S) ∪ e '' K) p q := by
  have hSJ : S ⊆ J := hunion ▸ subset_union_left
  have hKJ : K ⊆ J := hunion ▸ subset_union_right
  have hmeJ : J ∩ e '' J = {p, e p} := by rw [heJ, hJ.inter_eq]
  have hpK : p ∉ K := by
    intro hp
    have hpq : p = q := mem_singleton_iff.mp (hinter ▸ ⟨hS.left_mem, hp⟩)
    exact hS.ne hpq
  have hepS : e p ∉ S := by
    intro hep
    have hepq : e p = q := mem_singleton_iff.mp (hinter ▸ ⟨hep, hK.right_mem⟩)
    exact hK.ne hepq.symm
  have hepEK : e p ∉ e '' K := by
    rintro ⟨x, hx, hxp⟩
    exact hpK (e.injective hxp ▸ hx)
  have hKEs : ∀ z ∈ K, z ∈ e '' S → z = e p := by
    intro z hzK hzES
    have hzpair : z ∈ ({p, e p} : Set Plane) :=
      hmeJ ▸ ⟨hKJ hzK, image_mono hSJ hzES⟩
    rcases hzpair with rfl | hz
    · exact False.elim (hpK hzK)
    · exact hz
  have hmeetSecond : ∀ z ∈ K ∪ e '' S, z ∈ e '' K → z = e q := by
    intro z hz hzEK
    rcases hz with hzK | hzES
    · have hzpair : z ∈ ({p, e p} : Set Plane) :=
        hmeJ ▸ ⟨hKJ hzK, image_mono hKJ hzEK⟩
      rcases hzpair with rfl | hz
      · exact False.elim (hpK hzK)
      · exact False.elim (hepEK (hz ▸ hzEK))
    · obtain ⟨s, hs, rfl⟩ := hzES
      obtain ⟨k, hk, hks⟩ := hzEK
      have hks' : k = s := e.injective hks
      have hsq : s = q := mem_singleton_iff.mp (hinter ▸ ⟨hs, hks' ▸ hk⟩)
      exact congrArg e hsq
  have hES : IsArcBetween (e '' S) (e p) (e q) := hS.image_homeomorph e
  have hEK : IsArcBetween (e '' K) (e q) p := by
    simpa only [hinv p] using hK.image_homeomorph e
  have hL : IsArcBetween ((K ∪ e '' S) ∪ e '' K) q p :=
    (hK.concatenate hES hKEs).concatenate hEK hmeetSecond
  have hwhole : S ∪ ((K ∪ e '' S) ∪ e '' K) = C := by
    calc
      S ∪ ((K ∪ e '' S) ∪ e '' K) = (S ∪ K) ∪ (e '' S ∪ e '' K) := by
        ext z
        simp only [mem_union]
        tauto
      _ = J ∪ e '' J := by rw [← image_union, hunion]
      _ = C := by rw [heJ, hJ.union_eq]
  have hSL : S ∩ ((K ∪ e '' S) ∪ e '' K) = {p, q} := by
    apply Subset.antisymm
    · rintro z ⟨hzS, (hzK | hzES) | hzEK⟩
      · exact Or.inr (mem_singleton_iff.mp (hinter ▸ ⟨hzS, hzK⟩))
      · have hzpair : z ∈ ({p, e p} : Set Plane) :=
          hmeJ ▸ ⟨hSJ hzS, image_mono hSJ hzES⟩
        rcases hzpair with hz | hz
        · exact Or.inl hz
        · exact False.elim (hepS (hz ▸ hzS))
      · have hzpair : z ∈ ({p, e p} : Set Plane) :=
          hmeJ ▸ ⟨hSJ hzS, image_mono hKJ hzEK⟩
        rcases hzpair with hz | hz
        · exact Or.inl hz
        · exact False.elim (hepS (hz ▸ hzS))
    · exact pair_subset
        ⟨hS.left_mem, Or.inr ⟨e p, hK.right_mem, hinv p⟩⟩
        ⟨hS.right_mem, Or.inl (Or.inl hK.left_mem)⟩
  exact ⟨⟨hS, hL.reverse, hwhole, hSL⟩, ⟨K, hK, rfl, hKEs, hmeetSecond⟩⟩

/-- For non-antipodal cut endpoints, exactly one of the two named boundary
arcs can be the short arc; one of the two corresponding bridge decompositions exists. -/
theorem cutPair_has_antipodal_bridge {C M N : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (e : Plane ≃ₜ Plane) (he : e '' C = C)
    (hinv : Function.Involutive e) (hfree : ∀ x ∈ C, e x ≠ x)
    (hcut : IsCutPair C p q M N) (hq : q ≠ e p) :
    HasAntipodalBridge e M N p q ∨ HasAntipodalBridge e N M p q := by
  have hpC : p ∈ C := hcut.fst_subset hcut.fst.left_mem
  have hqC : q ∈ C := hcut.fst_subset hcut.fst.right_mem
  have hepC : e p ∈ C := he ▸ mem_image_of_mem e hpC
  obtain ⟨J₁, J₂, hhalf⟩ := exists_isCutPair hC hpC hepC (hfree p hpC).symm
  have hex : ∃ J J', IsCutPair C p (e p) J J' ∧ q ∈ J := by
    have hqm : q ∈ J₁ ∪ J₂ := hhalf.union_eq ▸ hqC
    rcases hqm with hq1 | hq2
    · exact ⟨J₁, J₂, hhalf, hq1⟩
    · exact ⟨J₂, J₁, hhalf.symm, hq2⟩
  obtain ⟨J, J', hhalf, hqJ⟩ := hex
  obtain ⟨S, K, hS, hK, hSK, hmeet⟩ :=
    hhalf.fst.exists_split hqJ hcut.fst.ne.symm hq
  have heJ := hhalf.image_fst_eq_snd_of_free_involution e he hinv hfree
  obtain ⟨hnew, hbridge⟩ := bridge_from_split e hinv hhalf heJ hS hK hSK hmeet
  have hSC : S ⊆ C := fun x hx => hhalf.fst_subset (hSK ▸ Or.inl hx)
  rcases hcut.arc_eq_fst_or_snd hS hSC with hSM | hSN
  · subst S
    have hLn : (K ∪ e '' M) ∪ e '' K = N := by
      rcases hcut.arc_eq_fst_or_snd hnew.snd hnew.snd_subset with hLM | hLN
      · exact False.elim (hnew.ne hLM.symm)
      · exact hLN
    exact Or.inl (hLn ▸ hbridge)
  · subst S
    have hLm : (K ∪ e '' N) ∪ e '' K = M := by
      rcases hcut.arc_eq_fst_or_snd hnew.snd hnew.snd_subset with hLM | hLN
      · exact hLM
      · exact False.elim (hnew.ne hLN.symm)
    exact Or.inr (hLm ▸ hbridge)

end Puzzling139335
