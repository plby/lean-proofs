import Wikipedia.NoExoticSixSphere.SimplicialCoefficientChains
import Wikipedia.NoExoticSixSphere.ShortExactCokernelRows
import Mathlib.Algebra.Homology.CommSq
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# The actual native chain sequence of two simplicial subcomplexes

The union square of subcomplexes is a pushout. Applying the original chain
functor with any coefficient module gives the difference-and-sum short
exact sequence. Its inclusion into the split ambient sequence is an
actual map of short complexes. The snake lemma therefore gives a short
exact cokernel row, the chain-level relative Mayer–Vietoris construction.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SimplicialCoefficients

section Algebra

variable {C : Type*} [Category* C] [Abelian C]
  {I A B T : C} {f : I ⟶ A} {g : I ⟶ B} {u : A ⟶ T} {v : B ⟶ T}

/-- A pushout square with a monic first map gives the actual short exact difference/sum row. -/
theorem pushout_shortExact (sq : IsPushout f g u v) [Mono f] : sq.shortComplex.ShortExact := by
  have hm : Mono (biprod.lift f (-g)) := by
    apply mono_of_mono_fac (biprod.lift_fst f (-g))
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ sq.isColimitCokernelCofork
    mono_f := hm
    epi_g := sq.epi_shortComplex_g }

end Algebra

variable (R : ModuleCat.{0} ℤ) {X : SSet.{0}} (A B : X.Subcomplex)

/-- The original native chain image of the intersection/union square. -/
theorem subcomplexSquare :
    IsPushout
      ((chains R).map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)))
      ((chains R).map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)))
      ((chains R).map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)))
      ((chains R).map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))) :=
  (chains R).map_isPushout
    (SSet.Subcomplex.BicartSq.isPushout
      (show SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from ⟨rfl, rfl⟩))

/-- Difference of the actual intersection inclusions, followed by the sum into the actual union. -/
abbrev subcomplexSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  (subcomplexSquare R A B).shortComplex

theorem subcomplexSequence_shortExact : (subcomplexSequence R A B).ShortExact :=
  pushout_shortExact (subcomplexSquare R A B)

/-- The split ambient difference-and-sum sequence. -/
abbrev ambientSequence (X : SSet.{0}) : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk
    (biprod.lift (𝟙 ((chains R).obj X)) (-(𝟙 ((chains R).obj X))))
    (biprod.desc (𝟙 ((chains R).obj X)) (𝟙 ((chains R).obj X)))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, Category.id_comp, add_neg_cancel])

theorem ambientSequence_shortExact (X : SSet.{0}) : (ambientSequence R X).ShortExact :=
  pushout_shortExact (IsPushout.of_id_fst (f := 𝟙 ((chains R).obj X)))

/-- Inclusion of the original intersection, two pieces, and union into the ambient chain row. -/
def inclusionSequenceMap : subcomplexSequence R A B ⟶ ambientSequence R X where
  τ₁ := (chains R).map (A ⊓ B).ι
  τ₂ := biprod.map ((chains R).map A.ι) ((chains R).map B.ι)
  τ₃ := (chains R).map (A ⊔ B).ι
  comm₁₂ := by
    change (chains R).map (A ⊓ B).ι ≫
        biprod.lift (𝟙 ((chains R).obj X)) (-(𝟙 ((chains R).obj X))) =
      biprod.lift
        ((chains R).map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)))
        (-((chains R).map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)))) ≫
        biprod.map ((chains R).map A.ι) ((chains R).map B.ι)
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, Category.comp_id,
        biprod.map_fst, biprod.lift_fst_assoc]
      rw [← Functor.map_comp]
      rfl
    · simp only [Category.assoc, biprod.lift_snd, Preadditive.comp_neg, Category.comp_id,
        biprod.map_snd, biprod.lift_snd_assoc, Preadditive.neg_comp]
      rw [← Functor.map_comp]
      rfl
  comm₂₃ := by
    change biprod.map ((chains R).map A.ι) ((chains R).map B.ι) ≫
        biprod.desc (𝟙 ((chains R).obj X)) (𝟙 ((chains R).obj X)) =
      biprod.desc
        ((chains R).map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)))
        ((chains R).map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))) ≫
        (chains R).map (A ⊔ B).ι
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, Category.comp_id,
        biprod.inl_desc_assoc]
      rw [← Functor.map_comp]
      rfl
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, Category.comp_id,
        biprod.inr_desc_assoc]
      rw [← Functor.map_comp]
      rfl

/-- The actual cokernel row is short exact, for every coefficient module. -/
theorem inclusionCokernel_shortExact : (cokernel (inclusionSequenceMap R A B)).ShortExact := by
  have : Mono (inclusionSequenceMap R A B).τ₃ :=
    inferInstanceAs (Mono ((chains R).map (A ⊔ B).ι))
  exact ShortExactCokernelRows.cokernel_shortExact (inclusionSequenceMap R A B)
    (subcomplexSequence_shortExact R A B) (ambientSequence_shortExact R X)

end NoExoticSixSphere.SimplicialCoefficients
