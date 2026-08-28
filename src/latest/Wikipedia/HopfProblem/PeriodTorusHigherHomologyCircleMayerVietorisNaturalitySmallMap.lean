import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsExact

/-!
# Naturality of the actual small-chain subcomplex

A continuous map carrying each member of one pair of subsets into the
corresponding member of another pair restricts to a map of the genuine
small-chain complexes. Its inclusion squares commute with the actual
singular-chain maps. No openness or covering assumption is needed.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict a continuous map to subsets which it carries into one another. -/
def coverRestriction (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    C(A, B) :=
  ⟨fun x => ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The restriction to the actual intersection of the two subsets. -/
def intersectionRestriction (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    C((U ∩ V : Set X), (U' ∩ V' : Set Y)) :=
  coverRestriction f (U ∩ V) (U' ∩ V') (fun _ hx => ⟨hfU hx.1, hfV hx.2⟩)

/-- Restriction commutes with the actual singular-chain maps of ambient inclusions. -/
theorem coverRestriction_ambient (f : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) :
    singularChainMap (coverRestriction f A B hf) ≫
        singularChainMap (subtypeInclusion B) =
      singularChainMap (subtypeInclusion A) ≫ singularChainMap f := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ))
  have h₁ := F.map_comp (TopCat.ofHom (coverRestriction f A B hf))
    (TopCat.ofHom (subtypeInclusion B))
  have h₂ := F.map_comp (TopCat.ofHom (subtypeInclusion A)) (TopCat.ofHom f)
  exact h₁.symm.trans h₂

/-- The left intersection square consists of the actual induced chain maps. -/
theorem coverRestriction_intersection_left (f : C(X, Y))
    (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    intersectionToLeft U V ≫ singularChainMap (coverRestriction f U U' hfU) =
      singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        intersectionToLeft U' V' := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ))
  have h₁ := F.map_comp
    (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)))
    (TopCat.ofHom (coverRestriction f U U' hfU))
  have h₂ := F.map_comp (TopCat.ofHom (intersectionRestriction f U V U' V' hfU hfV))
    (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U' ∩ V' ⊆ U')))
  exact h₁.symm.trans h₂

/-- The right intersection square consists of the actual induced chain maps. -/
theorem coverRestriction_intersection_right (f : C(X, Y))
    (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    intersectionToRight U V ≫ singularChainMap (coverRestriction f V V' hfV) =
      singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        intersectionToRight U' V' := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ))
  have h₁ := F.map_comp
    (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)))
    (TopCat.ofHom (coverRestriction f V V' hfV))
  have h₂ := F.map_comp (TopCat.ofHom (intersectionRestriction f U V U' V' hfU hfV))
    (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U' ∩ V' ⊆ V')))
  exact h₁.symm.trans h₂

/-- The actual induced chain map carries small chains to small chains. -/
theorem inducedChain_mem_small_of_mapsTo (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')
    (n : ℕ) (c : Chains X n) (hc : c ∈ smallChainSubmodule U V n) :
    inducedChain f n c ∈ smallChainSubmodule U' V' n := by
  have hle : smallChainSubmodule U V n ≤
      (smallChainSubmodule U' V' n).comap (inducedChain f n) := by
    rw [smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change inducedChain f n (simplexChain X n σ) ∈ smallChainSubmodule U' V' n
    rw [inducedChain_simplex]
    apply simplexChain_mem_small
    rcases hσ with hσ | hσ
    · left
      rintro _ ⟨s, rfl⟩
      exact hfU (hσ ⟨s, rfl⟩)
    · right
      rintro _ ⟨s, rfl⟩
      exact hfV (hσ ⟨s, rfl⟩)
  exact hle hc

/-- The genuine small-chain map induced by a map of the two pairs of subsets. -/
def smallMapOfMapsTo (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    smallComplex U V ⟶ smallComplex U' V' :=
  liftToSmall U' V' (smallInclusion U V ≫ singularChainMap f) (fun n c =>
    inducedChain_mem_small_of_mapsTo f U V U' V' hfU hfV n c.1 c.2)

@[simp] theorem smallMapOfMapsTo_f_val (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')
    (n : ℕ) (c : (smallComplex U V).X n) :
    ((smallMapOfMapsTo f U V U' V' hfU hfV).f n c).1 = inducedChain f n c.1 := rfl

/-- The small-chain map is a restriction of the actual ambient chain map. -/
@[simp] theorem smallMapOfMapsTo_inclusion (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V' =
      smallInclusion U V ≫ singularChainMap f :=
  liftToSmall_inclusion U' V' _ _

/-- Naturality of the left subset's actual chain map into small chains. -/
theorem toSmallLeft_smallMapOfMapsTo (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    toSmallLeft U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV =
      singularChainMap (coverRestriction f U U' hfU) ≫ toSmallLeft U' V' := by
  apply (cancel_mono (smallInclusion U' V')).mp
  calc
    (toSmallLeft U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV) ≫ smallInclusion U' V' =
        toSmallLeft U V ≫
          (smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V') :=
      Category.assoc _ _ _
    _ = toSmallLeft U V ≫ (smallInclusion U V ≫ singularChainMap f) :=
      congrArg (toSmallLeft U V ≫ ·) (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV)
    _ = (toSmallLeft U V ≫ smallInclusion U V) ≫ singularChainMap f :=
      (Category.assoc _ _ _).symm
    _ = singularChainMap (subtypeInclusion U) ≫ singularChainMap f :=
      congrArg (· ≫ singularChainMap f) (toSmallLeft_inclusion U V)
    _ = singularChainMap (coverRestriction f U U' hfU) ≫
        singularChainMap (subtypeInclusion U') := (coverRestriction_ambient f U U' hfU).symm
    _ = singularChainMap (coverRestriction f U U' hfU) ≫
        (toSmallLeft U' V' ≫ smallInclusion U' V') :=
      congrArg (singularChainMap (coverRestriction f U U' hfU) ≫ ·)
        (toSmallLeft_inclusion U' V').symm
    _ = (singularChainMap (coverRestriction f U U' hfU) ≫ toSmallLeft U' V') ≫
        smallInclusion U' V' := (Category.assoc _ _ _).symm

/-- Naturality of the right subset's actual chain map into small chains. -/
theorem toSmallRight_smallMapOfMapsTo (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    toSmallRight U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV =
      singularChainMap (coverRestriction f V V' hfV) ≫ toSmallRight U' V' := by
  apply (cancel_mono (smallInclusion U' V')).mp
  calc
    (toSmallRight U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV) ≫ smallInclusion U' V' =
        toSmallRight U V ≫
          (smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V') :=
      Category.assoc _ _ _
    _ = toSmallRight U V ≫ (smallInclusion U V ≫ singularChainMap f) :=
      congrArg (toSmallRight U V ≫ ·) (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV)
    _ = (toSmallRight U V ≫ smallInclusion U V) ≫ singularChainMap f :=
      (Category.assoc _ _ _).symm
    _ = singularChainMap (subtypeInclusion V) ≫ singularChainMap f :=
      congrArg (· ≫ singularChainMap f) (toSmallRight_inclusion U V)
    _ = singularChainMap (coverRestriction f V V' hfV) ≫
        singularChainMap (subtypeInclusion V') := (coverRestriction_ambient f V V' hfV).symm
    _ = singularChainMap (coverRestriction f V V' hfV) ≫
        (toSmallRight U' V' ≫ smallInclusion U' V') :=
      congrArg (singularChainMap (coverRestriction f V V' hfV) ≫ ·)
        (toSmallRight_inclusion U' V').symm
    _ = (singularChainMap (coverRestriction f V V' hfV) ≫ toSmallRight U' V') ≫
        smallInclusion U' V' := (Category.assoc _ _ _).symm

end Wikipedia.HopfProblem.SingularMayerVietoris
