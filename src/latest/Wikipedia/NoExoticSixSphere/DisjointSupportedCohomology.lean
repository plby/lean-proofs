import Wikipedia.NoExoticSixSphere.EmptySupportedCohomology
import Wikipedia.NoExoticSixSphere.SupportedModTwoConnectingExact

/-!
# Original cohomology splits over disjoint closed supports

Empty-support vanishing and the original Mayer--Vietoris maps prove
that summing the two actual support extensions is bijective. Both
directions of the proof concern these original extension maps, not
an abstract assignment of cohomology to a disjoint union.
-/

noncomputable section

open Wikipedia.HopfProblem

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X] (K L : Set X)

/-- Sum the original extension maps from the two supports. -/
def unionSum (p : ℕ) : (Cohomology K p × Cohomology L p) →ₗ[ℤ] Cohomology (K ∪ L) p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((extend (Set.subset_union_left : K ⊆ K ∪ L) p).toAddMonoidHom.comp (AddMonoidHom.fst _ _) +
      (extend (Set.subset_union_right : L ⊆ K ∪ L) p).toAddMonoidHom.comp (AddMonoidHom.snd _ _))

theorem unionSum_apply (p : ℕ) (a : Cohomology K p) (b : Cohomology L p) :
    unionSum K L p (a, b) = extend Set.subset_union_left p a +
      extend Set.subset_union_right p b := rfl

variable (hK : IsClosed K) (hL : IsClosed L) (hdis : Disjoint K L)

include hdis in
/-- The intersection is genuinely empty, so its original cohomology vanishes. -/
theorem disjoint_inter_subsingleton (p : ℕ) : Subsingleton (Cohomology (K ∩ L) p) := by
  rw [Set.disjoint_iff_inter_eq_empty.mp hdis]
  exact cohomology_empty_subsingleton X p

include hK hL hdis in
/-- A zero sum of disjoint supported classes has both original components zero. -/
theorem unionSum_eq_zero (p : ℕ) (a : Cohomology K p × Cohomology L p)
    (ha : unionSum K L p a = 0) : a = 0 := by
  have he : extend (Set.subset_union_left : K ⊆ K ∪ L) p a.1 =
      extend (Set.subset_union_right : L ⊆ K ∪ L) p (-a.2) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left ha
  obtain ⟨c, hc₁, hc₂⟩ := exists_intersection_lift K L hK hL p a.1 (-a.2) he
  have hc : c = 0 := (disjoint_inter_subsingleton K L hdis p).elim c 0
  have h₁ : a.1 = 0 := hc₁.symm.trans
    ((congrArg (extend (Set.inter_subset_left : K ∩ L ⊆ K) p) hc).trans (map_zero _))
  have h₂ : -a.2 = 0 := hc₂.symm.trans
    ((congrArg (extend (Set.inter_subset_right : K ∩ L ⊆ L) p) hc).trans (map_zero _))
  exact Prod.ext h₁ (neg_eq_zero.mp h₂)

include hK hL hdis in
/-- The original extension sum is injective for disjoint closed supports. -/
theorem unionSum_injective (p : ℕ) : Function.Injective (unionSum K L p) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply unionSum_eq_zero K L hK hL hdis p
  rw [map_sub, hab, sub_self]

include hK hL hdis in
/-- Every original union-supported class splits into two actual supported classes. -/
theorem unionSum_surjective (p : ℕ) : Function.Surjective (unionSum K L p) := by
  intro c
  have hz : connecting K L hK hL p c = 0 :=
    (disjoint_inter_subsingleton K L hdis (p + 1)).elim _ _
  obtain ⟨a, ha⟩ := (connecting_exact_right K L hK hL p).ge hz
  refine ⟨(a.1, -a.2), ?_⟩
  rw [unionSum_apply, map_neg]
  change extend (Set.subset_union_left : K ⊆ K ∪ L) p a.1 -
    extend (Set.subset_union_right : L ⊆ K ∪ L) p a.2 = c at ha
  simpa only [sub_eq_add_neg] using ha

/-- The inverse is supplied by proved exactness of the actual support maps. -/
def disjointUnionEquiv (p : ℕ) :
    (Cohomology K p × Cohomology L p) ≃ₗ[ℤ] Cohomology (K ∪ L) p :=
  LinearEquiv.ofBijective (unionSum K L p)
    ⟨unionSum_injective K L hK hL hdis p, unionSum_surjective K L hK hL hdis p⟩

theorem disjointUnionEquiv_apply (p : ℕ) (a : Cohomology K p) (b : Cohomology L p) :
    disjointUnionEquiv K L hK hL hdis p (a, b) =
      extend Set.subset_union_left p a + extend Set.subset_union_right p b := rfl

include hK hL hdis in
/-- Splitting with the union named separately retains the specified original inclusions. -/
theorem exists_sum_of_disjoint_union {S : Set X} (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hS : K ∪ L = S) (p : ℕ) (a : Cohomology S p) :
    ∃ b : Cohomology K p, ∃ c : Cohomology L p,
      extend hKS p b + extend hLS p c = a := by
  subst S
  obtain ⟨⟨b, c⟩, he⟩ := unionSum_surjective K L hK hL hdis p a
  exact ⟨b, c, he⟩

include hK hL hdis in
/-- Original disjoint-supported summands are uniquely determined, also after naming the union. -/
theorem sum_ext_of_disjoint_union {S : Set X} (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hS : K ∪ L = S) (p : ℕ) (a a' : Cohomology K p) (b b' : Cohomology L p)
    (he : extend hKS p a + extend hLS p b = extend hKS p a' + extend hLS p b') :
    a = a' ∧ b = b' := by
  subst S
  have he' : unionSum K L p (a, b) = unionSum K L p (a', b') := he
  have h := unionSum_injective K L hK hL hdis p he'
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end NoExoticSixSphere.SupportedModTwoCohomology
