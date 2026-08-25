import Wikipedia.SchoenfliesTheorem.FaceCyclesProof
import Wikipedia.SchoenfliesTheorem.GeneralCrosscut

/-!
# Relative neighborhoods along Jordan subarcs

An arc contained in a Jordan curve is one of the two arcs cut out by its
endpoints.  Consequently, away from its endpoints it contains a neighborhood
relative to the whole Jordan curve.
-/

open Set

namespace Schoenflies

/-- An arc on a Jordan curve agrees with one of the two arcs between its
endpoints. -/
theorem IsCutPair.arc_eq_fst_or_snd {C A A₁ A₂ : Set Plane} {p q : Plane}
    (hcut : IsCutPair C p q A₁ A₂) (hA : IsArcBetween A p q) (hsub : A ⊆ C) :
    A = A₁ ∨ A = A₂ := by
  have extend_subset (E : Set Plane) (hp : p ∈ E) (hq : q ∈ E)
      (hs : A \ {p, q} ⊆ E) : A ⊆ E := by
    intro z hz
    by_cases hends : z ∈ ({p, q} : Set Plane)
    · rcases mem_insert_iff.mp hends with rfl | hq'
      · exact hp
      · obtain rfl := mem_singleton_iff.mp hq'
        exact hq
    · exact hs ⟨hz, hends⟩
  by_cases hS₁ : A \ {p, q} ⊆ A₁
  · exact Or.inl (hcut.fst.eq_of_subset hA
      (extend_subset A₁ hcut.fst.left_mem hcut.fst.right_mem hS₁))
  · obtain ⟨z, hz, hz₁⟩ := Set.not_subset.mp hS₁
    have hopen : A \ {p, q} ⊆ A₁ᶜ ∪ A₂ᶜ := by
      intro w hw
      by_cases hw₁ : w ∈ A₁
      · right
        intro hw₂
        exact hw.2 (hcut.inter_eq ▸ (show w ∈ A₁ ∩ A₂ from ⟨hw₁, hw₂⟩))
      · exact Or.inl hw₁
    have hS₂ : A \ {p, q} ⊆ A₂ := by
      intro y hy
      by_contra hy₂
      obtain ⟨w, hw, hw₁, hw₂⟩ := hA.isPreconnected_diff A₁ᶜ A₂ᶜ
        hcut.fst.isArc.isClosed.isOpen_compl hcut.snd.isArc.isClosed.isOpen_compl
        hopen ⟨z, hz, hz₁⟩ ⟨y, hy, hy₂⟩
      have hwC := hsub hw.1
      rw [← hcut.union_eq] at hwC
      exact hwC.elim hw₁ hw₂
    exact Or.inr (hcut.snd.eq_of_subset hA
      (extend_subset A₂ hcut.snd.left_mem hcut.snd.right_mem hS₂))

/-- Any prescribed arc on a Jordan curve has a complementary arc with the same
endpoints. -/
theorem IsJordanCurve.exists_cutPair_of_subset_arc {C A : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A p q) (hsub : A ⊆ C) :
    ∃ B, IsCutPair C p q A B := by
  have hpq : p ≠ q := by
    obtain ⟨f, _, hi, _, h0, h1⟩ := hA
    intro heq
    exact zero_ne_one (hi zero_mem_I one_mem_I
      (h0.trans (heq.trans h1.symm)))
  obtain ⟨A₁, A₂, hcut⟩ :=
    exists_isCutPair hC (hsub hA.left_mem) (hsub hA.right_mem) hpq
  rcases hcut.arc_eq_fst_or_snd hA hsub with rfl | rfl
  · exact ⟨A₂, hcut⟩
  · exact ⟨A₁, hcut.symm⟩

/-- Away from the two endpoints, an arc on a Jordan curve contains a small
ball intersected with that curve. -/
theorem IsJordanCurve.exists_ball_inter_subset_arc {C A : Set Plane} {p q x : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A p q) (hsub : A ⊆ C)
    (hx : x ∈ A \ {p, q}) :
    ∃ r > 0, Metric.ball x r ∩ C ⊆ A := by
  obtain ⟨B, hcut⟩ := hC.exists_cutPair_of_subset_arc hA hsub
  have hxB : x ∉ B := by
    intro hxB
    exact hx.2 (hcut.inter_eq ▸ (show x ∈ A ∩ B from ⟨hx.1, hxB⟩))
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp hcut.snd.isArc.isClosed.isOpen_compl x hxB
  refine ⟨r, hr, ?_⟩
  rintro y ⟨hyball, hyC⟩
  rw [← hcut.union_eq] at hyC
  exact hyC.elim id (fun hyB => False.elim (hball hyball hyB))

end Schoenflies
