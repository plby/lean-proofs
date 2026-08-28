import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportedCohomologyConnecting

/-!
# Original integral closed-support Mayer--Vietoris exactness

The complement comparisons retain the actual intersection-extension
pair and the actual signed difference of union extensions. Original
relative exactness therefore gives all three range-kernel identities
for these supported integral groups, including the degree-zero start.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedCohomology

variable {X : Type} [TopologicalSpace X] (K L : Set X)

def intersectionMap (p : ℕ) : Cohomology (K ∩ L) p →ₗ[ℤ] (Cohomology K p × Cohomology L p) :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((extend (Set.inter_subset_left : K ∩ L ⊆ K) p).toAddMonoidHom.prod
      (extend (Set.inter_subset_right : K ∩ L ⊆ L) p).toAddMonoidHom)

/-- The integer minus sign is part of the original union-support map. -/
def unionDifference (p : ℕ) : (Cohomology K p × Cohomology L p) →ₗ[ℤ] Cohomology (K ∪ L) p :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((extend (Set.subset_union_left : K ⊆ K ∪ L) p).toAddMonoidHom.comp (AddMonoidHom.fst _ _) -
      (extend (Set.subset_union_right : L ⊆ K ∪ L) p).toAddMonoidHom.comp (AddMonoidHom.snd _ _))

theorem firstMap_interComplement (hK : IsClosed K) (hL : IsClosed L)
    (p : ℕ) (a : Cohomology (K ∩ L) p) :
    IntegralRelativeCohomologyMayerVietoris.firstMap Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
      (interComplementEquiv K L p a) = intersectionMap K L p a := by
  have h₁ := IntegralRelativeCohomologyMayerVietoris.setCongr_subset
    (rfl : Kᶜ = Kᶜ) (Set.compl_inter K L)
    (show Kᶜ ⊆ (K ∩ L)ᶜ from fun _ hx hy => hx hy.1) Set.subset_union_left p a
  have h₂ := IntegralRelativeCohomologyMayerVietoris.setCongr_subset
    (rfl : Lᶜ = Lᶜ) (Set.compl_inter K L)
    (show Lᶜ ⊆ (K ∩ L)ᶜ from fun _ hx hy => hx hy.2) Set.subset_union_right p a
  exact (IntegralRelativeCohomologyMayerVietoris.firstMap_apply
    Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
      (interComplementEquiv K L p a)).trans (Prod.ext h₁.symm h₂.symm)

theorem unionComplement_unionDifference (p : ℕ) (a : Cohomology K p × Cohomology L p) :
    unionComplementEquiv K L p (unionDifference K L p a) =
      IntegralRelativeCohomologyMayerVietoris.differenceMap Kᶜ Lᶜ p a := by
  have h₁ := IntegralRelativeCohomologyMayerVietoris.setCongr_subset
    (Set.compl_union K L) (rfl : Kᶜ = Kᶜ)
    (show (K ∪ L)ᶜ ⊆ Kᶜ from fun _ hx hy => hx (Or.inl hy)) Set.inter_subset_left p a.1
  have h₂ := IntegralRelativeCohomologyMayerVietoris.setCongr_subset
    (Set.compl_union K L) (rfl : Lᶜ = Lᶜ)
    (show (K ∪ L)ᶜ ⊆ Lᶜ from fun _ hx hy => hx (Or.inr hy)) Set.inter_subset_right p a.2
  change unionComplementEquiv K L p
    (extend Set.subset_union_left p a.1 - extend Set.subset_union_right p a.2) = _
  exact ((unionComplementEquiv K L p).map_sub _ _).trans
    ((congrArg₂ (fun x y => x - y) h₁ h₂).trans
      (IntegralRelativeCohomologyMayerVietoris.differenceMap_apply Kᶜ Lᶜ p a.1 a.2).symm)

variable (hK : IsClosed K) (hL : IsClosed L)

theorem connecting_exact_left (p : ℕ) :
    LinearMap.range (connecting K L hK hL p) = LinearMap.ker (intersectionMap K L (p + 1)) := by
  let I := interComplementEquiv K L (p + 1)
  let W := unionComplementEquiv K L p
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : IntegralRelativeCohomologyMayerVietoris.firstMap
        Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl (p + 1) (I (connecting K L hK hL p b)) = 0 := by
      rw [connecting_toRelative]
      exact (IntegralRelativeCohomologyMayerVietoris.exact_left
        Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).le ⟨W b, rfl⟩
    exact (firstMap_interComplement K L hK hL (p + 1) (connecting K L hK hL p b)).symm.trans hb
  · intro ha
    have ha' : I a ∈ LinearMap.ker
        (IntegralRelativeCohomologyMayerVietoris.firstMap
          Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl (p + 1)) :=
      (firstMap_interComplement K L hK hL (p + 1) a).trans ha
    obtain ⟨b, hb⟩ := (IntegralRelativeCohomologyMayerVietoris.exact_left
      Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).ge ha'
    refine ⟨W.symm b, I.injective ?_⟩
    apply (connecting_toRelative K L hK hL p (W.symm b)).trans
    exact (congrArg (IntegralRelativeCohomologyMayerVietoris.connecting
      Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p) (W.apply_symm_apply b)).trans hb

include hK hL in
theorem intersection_exact_middle (p : ℕ) :
    LinearMap.range (intersectionMap K L p) = LinearMap.ker (unionDifference K L p) := by
  let I := interComplementEquiv K L p
  let W := unionComplementEquiv K L p
  let f := IntegralRelativeCohomologyMayerVietoris.firstMap
    Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
  let g := IntegralRelativeCohomologyMayerVietoris.differenceMap Kᶜ Lᶜ p
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    apply W.injective
    calc
      _ = g (intersectionMap K L p b) := unionComplement_unionDifference K L p _
      _ = g (f (I b)) := congrArg g (firstMap_interComplement K L hK hL p b).symm
      _ = 0 := (IntegralRelativeCohomologyMayerVietoris.exact_middle
        Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).le ⟨I b, rfl⟩
      _ = _ := W.map_zero.symm
  · intro ha
    have ha' : g a = 0 := (unionComplement_unionDifference K L p a).symm.trans
      ((congrArg W ha).trans W.map_zero)
    obtain ⟨b, hb⟩ := (IntegralRelativeCohomologyMayerVietoris.exact_middle
      Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).ge ha'
    refine ⟨I.symm b, ?_⟩
    exact (firstMap_interComplement K L hK hL p (I.symm b)).symm.trans
      ((congrArg f (I.apply_symm_apply b)).trans hb)

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
    apply (congrArg (IntegralRelativeCohomologyMayerVietoris.connecting
      Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p) (unionComplement_unionDifference K L p b)).trans
    have hb : IntegralRelativeCohomologyMayerVietoris.connecting
        Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
        (IntegralRelativeCohomologyMayerVietoris.differenceMap Kᶜ Lᶜ p b) = 0 :=
      (IntegralRelativeCohomologyMayerVietoris.exact_right
        Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).le ⟨b, rfl⟩
    exact hb.trans I.map_zero.symm
  · intro ha
    have ha' : W a ∈ LinearMap.ker (IntegralRelativeCohomologyMayerVietoris.connecting
        Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p) :=
      (connecting_toRelative K L hK hL p a).symm.trans ((congrArg I ha).trans I.map_zero)
    obtain ⟨b, hb⟩ := (IntegralRelativeCohomologyMayerVietoris.exact_right
      Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).ge ha'
    exact ⟨b, W.injective ((unionComplement_unionDifference K L p b).trans hb)⟩

include hK hL in
theorem intersectionMap_zero_injective : Function.Injective (intersectionMap K L 0) := by
  intro a b hab
  apply (interComplementEquiv K L 0).injective
  apply IntegralRelativeCohomologyMayerVietoris.firstMap_zero_injective
    Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl
  exact (firstMap_interComplement K L hK hL 0 a).trans
    (hab.trans (firstMap_interComplement K L hK hL 0 b).symm)

include hK hL in
/-- Equal original extensions lift together from the actual intersection support. -/
theorem exists_intersection_lift (p : ℕ) (a : Cohomology K p) (b : Cohomology L p)
    (hab : extend (Set.subset_union_left : K ⊆ K ∪ L) p a =
      extend (Set.subset_union_right : L ⊆ K ∪ L) p b) :
    ∃ c : Cohomology (K ∩ L) p,
      extend (Set.inter_subset_left : K ∩ L ⊆ K) p c = a ∧
        extend (Set.inter_subset_right : K ∩ L ⊆ L) p c = b := by
  have hz : (a, b) ∈ LinearMap.ker (unionDifference K L p) := by
    change extend Set.subset_union_left p a - extend Set.subset_union_right p b = 0
    exact sub_eq_zero.mpr hab
  obtain ⟨c, hc⟩ := (intersection_exact_middle K L hK hL p).ge hz
  exact ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedCohomology
