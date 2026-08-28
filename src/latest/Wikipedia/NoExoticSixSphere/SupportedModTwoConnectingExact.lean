import Wikipedia.NoExoticSixSphere.SupportedModTwoConnecting

/-!
# Exactness adjacent to the original closed-support connecting map

The complement comparisons retain the original support-extension pair
and difference maps. Transporting the proved relative Mayer--Vietoris
exactness therefore proves both adjacent range-kernel identities on
the actual supported cohomology groups.
-/

noncomputable section

open Wikipedia.HopfProblem

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X] (K L : Set X)

/-- Both original extensions from the actual intersection support. -/
def intersectionMap (p : ℕ) : Cohomology (K ∩ L) p →ₗ[ℤ] (Cohomology K p × Cohomology L p) :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((extend (Set.inter_subset_left : K ∩ L ⊆ K) p).toAddMonoidHom.prod
      (extend (Set.inter_subset_right : K ∩ L ⊆ L) p).toAddMonoidHom)

/-- The original difference of extensions to the actual union support. -/
def unionDifference (p : ℕ) : (Cohomology K p × Cohomology L p) →ₗ[ℤ] Cohomology (K ∪ L) p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((extend (Set.subset_union_left : K ⊆ K ∪ L) p).toAddMonoidHom.comp (AddMonoidHom.fst _ _) -
      (extend (Set.subset_union_right : L ⊆ K ∪ L) p).toAddMonoidHom.comp (AddMonoidHom.snd _ _))

/-- The complement comparison retains both original intersection-support extensions. -/
theorem firstMap_interComplement (hK : IsClosed K) (hL : IsClosed L)
    (p : ℕ) (a : Cohomology (K ∩ L) p) :
    RelativeModTwoMayerVietoris.firstMap Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
      (interComplementEquiv K L p a) = intersectionMap K L p a := by
  have h₁ := RelativeModTwoCochains.setCongr_subset (rfl : Kᶜ = Kᶜ) (Set.compl_inter K L)
    (show Kᶜ ⊆ (K ∩ L)ᶜ from fun _ hx hy => hx hy.1) Set.subset_union_left p a
  have h₂ := RelativeModTwoCochains.setCongr_subset (rfl : Lᶜ = Lᶜ) (Set.compl_inter K L)
    (show Lᶜ ⊆ (K ∩ L)ᶜ from fun _ hx hy => hx hy.2) Set.subset_union_right p a
  exact (RelativeModTwoMayerVietoris.firstMap_apply Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
    (interComplementEquiv K L p a)).trans (Prod.ext h₁.symm h₂.symm)

/-- The complement comparison retains the original difference of union-support extensions. -/
theorem unionComplement_unionDifference (p : ℕ) (a : Cohomology K p × Cohomology L p) :
    unionComplementEquiv K L p (unionDifference K L p a) =
      RelativeModTwoMayerVietoris.differenceMap Kᶜ Lᶜ p a := by
  have h₁ := RelativeModTwoCochains.setCongr_subset (Set.compl_union K L) (rfl : Kᶜ = Kᶜ)
    (show (K ∪ L)ᶜ ⊆ Kᶜ from fun _ hx hy => hx (Or.inl hy)) Set.inter_subset_left p a.1
  have h₂ := RelativeModTwoCochains.setCongr_subset (Set.compl_union K L) (rfl : Lᶜ = Lᶜ)
    (show (K ∪ L)ᶜ ⊆ Lᶜ from fun _ hx hy => hx (Or.inr hy)) Set.inter_subset_right p a.2
  change unionComplementEquiv K L p
    (extend Set.subset_union_left p a.1 - extend Set.subset_union_right p a.2) = _
  exact ((unionComplementEquiv K L p).map_sub _ _).trans
    ((congrArg₂ (fun x y => x - y) h₁ h₂).trans
      (RelativeModTwoMayerVietoris.differenceMap_apply Kᶜ Lᶜ p a.1 a.2).symm)

variable (hK : IsClosed K) (hL : IsClosed L)

/-- Exactness at the actual supported cohomology of the intersection. -/
theorem connecting_exact_left (p : ℕ) :
    LinearMap.range (connecting K L hK hL p) = LinearMap.ker (intersectionMap K L (p + 1)) := by
  let I := interComplementEquiv K L (p + 1)
  let W := unionComplementEquiv K L p
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : RelativeModTwoMayerVietoris.firstMap Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl
        (p + 1) (I (connecting K L hK hL p b)) = 0 := by
      rw [connecting_toRelative]
      exact (RelativeModTwoMayerVietoris.exact_left Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).le
        ⟨W b, rfl⟩
    exact (firstMap_interComplement K L hK hL (p + 1) (connecting K L hK hL p b)).symm.trans hb
  · intro ha
    have ha' : I a ∈ LinearMap.ker
        (RelativeModTwoMayerVietoris.firstMap Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl (p + 1)) :=
      (firstMap_interComplement K L hK hL (p + 1) a).trans ha
    obtain ⟨b, hb⟩ :=
      (RelativeModTwoMayerVietoris.exact_left Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).ge ha'
    refine ⟨W.symm b, I.injective ?_⟩
    apply (connecting_toRelative K L hK hL p (W.symm b)).trans
    exact (congrArg
      (RelativeModTwoMayerVietoris.connecting Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p)
      (W.apply_symm_apply b)).trans hb

/-- Exactness at the actual supported cohomology of the union. -/
theorem connecting_exact_right (p : ℕ) :
    LinearMap.range (unionDifference K L p) = LinearMap.ker (connecting K L hK hL p) := by
  let I := interComplementEquiv K L (p + 1)
  let W := unionComplementEquiv K L p
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    apply I.injective
    apply (connecting_toRelative K L hK hL p (unionDifference K L p b)).trans
    apply (congrArg
      (RelativeModTwoMayerVietoris.connecting Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p)
      (unionComplement_unionDifference K L p b)).trans
    have hb : RelativeModTwoMayerVietoris.connecting Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
        (RelativeModTwoMayerVietoris.differenceMap Kᶜ Lᶜ p b) = 0 :=
      (RelativeModTwoMayerVietoris.exact_right Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).le
        ⟨b, rfl⟩
    exact hb.trans I.map_zero.symm
  · intro ha
    have ha' : W a ∈ LinearMap.ker
        (RelativeModTwoMayerVietoris.connecting Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p) :=
      (connecting_toRelative K L hK hL p a).symm.trans ((congrArg I ha).trans I.map_zero)
    obtain ⟨b, hb⟩ :=
      (RelativeModTwoMayerVietoris.exact_right Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).ge ha'
    exact ⟨b, W.injective ((unionComplement_unionDifference K L p b).trans hb)⟩

end NoExoticSixSphere.SupportedModTwoCohomology
