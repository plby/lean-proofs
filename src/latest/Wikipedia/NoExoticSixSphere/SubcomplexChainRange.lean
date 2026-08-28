import Wikipedia.NoExoticSixSphere.SubcomplexChainSequence
import Wikipedia.NoExoticSixSphere.ChainBiproductElements
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Intersections of the actual subcomplex-chain images

For any coefficient module, a chain in both subcomplex images comes
from their intersection. The proof uses the original difference-and-sum
short exact sequence and injectivity of the union inclusion.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SimplicialCoefficients

variable (R : ModuleCat.{0} ℤ) {X : SSet.{0}}

/-- The degree map of the original subcomplex inclusion. -/
abbrev inclusionMap (A : X.Subcomplex) (n : ℕ) := ((chains R).map A.ι).f n

/-- The image in the original ambient chain module. -/
def chainImage (A : X.Subcomplex) (n : ℕ) : Submodule ℤ (((chains R).obj X).X n) :=
  LinearMap.range (inclusionMap R A n).hom

/-- Nested original inclusions compose to the original ambient inclusion. -/
theorem homOfLE_inclusion {A B : X.Subcomplex} (h : A ≤ B) :
    (chains R).map (SSet.Subcomplex.homOfLE h) ≫ (chains R).map B.ι =
      (chains R).map A.ι := by
  rw [← Functor.map_comp]
  rfl

theorem chainImage_mono {A B : X.Subcomplex} (h : A ≤ B) (n : ℕ) :
    chainImage R A n ≤ chainImage R B n := by
  rintro c ⟨a, ha⟩
  refine ⟨(((chains R).map (SSet.Subcomplex.homOfLE h)).f n).hom a, ?_⟩
  exact (congrArg (fun f => (f.f n).hom a) (homOfLE_inclusion R h)).trans ha

/-- The original sum map, followed by union inclusion, is the ambient sum map. -/
theorem subcomplexSequence_g_inclusion (A B : X.Subcomplex) :
    (subcomplexSequence R A B).g ≫ (chains R).map (A ⊔ B).ι =
      biprod.desc ((chains R).map A.ι) ((chains R).map B.ι) := by
  change biprod.desc
    ((chains R).map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)))
    ((chains R).map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))) ≫ _ = _
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, biprod.inl_desc]
    exact homOfLE_inclusion R le_sup_left
  · simp only [biprod.inr_desc_assoc, biprod.inr_desc]
    exact homOfLE_inclusion R le_sup_right

/-- The image of the simplicial union is the sum of the two actual chain images. -/
theorem chainImage_sup (A B : X.Subcomplex) (n : ℕ) :
    chainImage R (A ⊔ B) n = chainImage R A n ⊔ chainImage R B n := by
  apply le_antisymm _
    (sup_le (chainImage_mono R le_sup_left n) (chainImage_mono R le_sup_right n))
  rintro c ⟨a, ha⟩
  let S := subcomplexSequence R A B
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp
    (subcomplexSequence_shortExact R A B) n
  let : Epi (S.g.f n) := hd.epi_g
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (S.g.f n)).mp inferInstance a
  let l := ((biprod.fst : (chains R).obj A ⊞ (chains R).obj B ⟶
    (chains R).obj A).f n).hom b
  let r := ((biprod.snd : (chains R).obj A ⊞ (chains R).obj B ⟶
    (chains R).obj B).f n).hom b
  have hs := subcomplexSequence_g_inclusion R A B
  rw [biprod.desc_eq] at hs
  have he := congrArg (fun f => (f.f n).hom b) hs
  change (inclusionMap R (A ⊔ B) n).hom ((S.g.f n).hom b) =
    (inclusionMap R A n).hom l + (inclusionMap R B n).hom r at he
  exact Submodule.mem_sup.mpr ⟨_, ⟨l, rfl⟩, _, ⟨r, rfl⟩,
    he.symm.trans ((congrArg (inclusionMap R (A ⊔ B) n).hom hb).trans ha)⟩

/-- Intersecting actual chain images is the image of the actual intersection. -/
theorem chainImage_inf (A B : X.Subcomplex) (n : ℕ) :
    chainImage R (A ⊓ B) n = chainImage R A n ⊓ chainImage R B n := by
  apply le_antisymm
    (le_inf (chainImage_mono R inf_le_left n) (chainImage_mono R inf_le_right n))
  rintro c ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  let S := subcomplexSequence R A B
  let t : S.X₂.X n := ChainBiproduct.pair n a (-b)
  have he := congrArg (fun f => (f.f n).hom t) (subcomplexSequence_g_inclusion R A B)
  have ht : (S.g.f n).hom t = 0 := by
    apply (ModuleCat.mono_iff_injective (inclusionMap R (A ⊔ B) n)).mp inferInstance
    change (inclusionMap R (A ⊔ B) n).hom ((S.g.f n).hom t) =
      (inclusionMap R (A ⊔ B) n).hom 0
    rw [map_zero]
    refine he.trans ((ChainBiproduct.desc_pair
      ((chains R).map A.ι) ((chains R).map B.ι) n a (-b)).trans ?_)
    change (inclusionMap R A n).hom a + (inclusionMap R B n).hom (-b) = 0
    rw [map_neg, ha, hb, add_neg_cancel]
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp
    (subcomplexSequence_shortExact R A B) n
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp hd.exact t ht
  have hz' := congrArg
    (fun d => ((biprod.fst : (chains R).obj A ⊞ (chains R).obj B ⟶
      (chains R).obj A).f n).hom d) hz
  have hleft : (((chains R).map
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))).f n).hom z = a :=
    (ChainBiproduct.fst_lift
      ((chains R).map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)))
      (-((chains R).map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))))
      n z).symm.trans (hz'.trans (ChainBiproduct.fst_pair n a (-b)))
  refine ⟨z, ?_⟩
  exact (congrArg (fun f => (f.f n).hom z)
    (homOfLE_inclusion R (inf_le_left : A ⊓ B ≤ A))).symm.trans
      ((congrArg (inclusionMap R A n).hom hleft).trans ha)

end NoExoticSixSphere.SimplicialCoefficients
