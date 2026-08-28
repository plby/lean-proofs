import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafAugmentation
import Mathlib.Topology.Sheaves.Functors

/-!
# Pullback of the original singular cochain presheaves

A continuous map carries the actual preimage of each open subset to that
open subset. Dualizing the original singular chain maps gives a natural
transformation to the native presheaf pushforward. These transformations
commute with the actual cochain differentials, coefficient changes, and
the original constant augmentation.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

open FirstHurewicz

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The original continuous map restricted to the actual preimage of
an open subset, with its codomain restricted to that subset. -/
def preimageMap (U : Opens Y) : C((Opens.map f).obj U, U) where
  toFun x := ⟨f x.val, x.property⟩
  continuous_toFun := (f.hom.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem preimageMap_apply (U : Opens Y) (x : (Opens.map f).obj U) :
    preimageMap f U x = ⟨f x.val, x.property⟩ := rfl

/-- The actual preimage-to-open maps commute with the original open
inclusions as a natural transformation of topological spaces. -/
def preimageToOpen : Opens.map f ⋙ Opens.toTopCat X ⟶ Opens.toTopCat Y where
  app U := TopCat.ofHom (preimageMap f U)
  naturality U V r := by
    ext x
    rfl

/-- Literal restriction compatibility of the preimage-to-open maps. -/
theorem preimageMap_restrict {U V : Opens Y} (r : U ⟶ V) :
    (preimageMap f V).comp
        (((Opens.toTopCat X).map ((Opens.map f).map r)).hom) =
      (((Opens.toTopCat Y).map r).hom).comp (preimageMap f U) := by
  ext x
  rfl

variable (A : AddCommGrpCat.{0})

/-- The original continuous restriction square induces the corresponding
commutative square of native cochain complexes. -/
theorem openPullback_restrict {U V : Opens Y} (r : U ⟶ V) :
    singularPullback A (((Opens.toTopCat Y).map r).hom) ≫
        singularPullback A (preimageMap f U) =
      singularPullback A (preimageMap f V) ≫
        singularPullback A (((Opens.toTopCat X).map ((Opens.map f).map r)).hom) := by
  exact (singularPullback_comp A (preimageMap f U)
      (((Opens.toTopCat Y).map r).hom)).symm.trans
    ((congrArg (singularPullback A) (preimageMap_restrict f r).symm).trans
      (singularPullback_comp A
        (((Opens.toTopCat X).map ((Opens.map f).map r)).hom) (preimageMap f V)))

/-- The native pullback on original degreewise cochain presheaves.
Its target is Mathlib's actual presheaf pushforward. -/
def rawPullback (n : ℕ) : cochainPresheaf Y A n ⟶
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj (cochainPresheaf X A n) where
  app U := (singularPullback A (preimageMap f U.unop)).f n
  naturality U V r := by
    exact congrArg (fun g => g.f n) (openPullback_restrict f A r.unop)

/-- On every original open subset, the presheaf map is the genuine
singular cochain pullback by the preimage-to-open map. -/
@[simp] theorem rawPullback_app (n : ℕ) (U : Opens Y) :
    (rawPullback f A n).app (op U) = (singularPullback A (preimageMap f U)).f n := rfl

/-- The presheaf pullback is literal precomposition with the actual
singular chain map. -/
@[simp] theorem rawPullback_app_chain (n : ℕ) (U : Opens Y)
    (φ : Cochains U A n) (c : Chains ((Opens.map f).obj U) n) :
    DFunLike.coe (F := Cochains ((Opens.map f).obj U) A n)
        ((rawPullback f A n).app (op U) φ) c =
      φ (inducedChain (preimageMap f U) n c) := rfl

/-- Evaluation uses the original simplex composed with the actual
preimage-to-open map. -/
@[simp] theorem rawPullback_app_simplex (n : ℕ) (U : Opens Y)
    (φ : Cochains U A n) (σ : SingularSimplex ((Opens.map f).obj U) n) :
    DFunLike.coe (F := Cochains ((Opens.map f).obj U) A n)
        ((rawPullback f A n).app (op U) φ)
        (simplexChain ((Opens.map f).obj U) n σ) =
      φ (simplexChain U n ((preimageMap f U).comp σ)) :=
  singularPullback_simplex A (preimageMap f U) n φ σ

/-- Pullback commutes with restriction on the original cochain sections. -/
theorem rawPullback_restrict (n : ℕ) {U V : Opens Y} (r : U ⟶ V)
    (φ : Cochains V A n) :
    (rawPullback f A n).app (op U) ((cochainPresheaf Y A n).map r.op φ) =
      (cochainPresheaf X A n).map ((Opens.map f).map r).op
        ((rawPullback f A n).app (op V) φ) :=
  ConcreteCategory.congr_hom ((rawPullback f A n).naturality r.op) φ

/-- The actual presheaf pullback commutes with every native cochain
differential, including the zero differentials. -/
@[reassoc] theorem rawPullback_d (i j : ℕ) :
    rawPullback f A i ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map
          (presheafDifferential X A i j) =
      presheafDifferential Y A i j ≫ rawPullback f A j := by
  apply NatTrans.ext
  funext U
  exact (singularPullback A (preimageMap f U.unop)).comm i j

variable {A}

/-- Literal coefficient postcomposition commutes with the genuine
presheaf pullback. -/
@[reassoc] theorem rawPullback_coefficient {B : AddCommGrpCat.{0}} (α : A ⟶ B)
    (n : ℕ) :
    rawPullback f A n ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map
          (presheafCoefficientMap X α n) =
      presheafCoefficientMap Y α n ≫ rawPullback f B n := by
  apply NatTrans.ext
  funext U
  exact congrArg (fun g => g.f n) (coefficientMap_naturality α (preimageMap f U.unop))

variable (A)

/-- Pullback of the actual constant presheaf keeps the original
coefficient value on every open subset. -/
def rawConstantPullback : ConstantSheafFirstCohomology.Constant.presheaf Y A ⟶
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).obj
      (ConstantSheafFirstCohomology.Constant.presheaf X A) where
  app _ := 𝟙 A
  naturality _ _ _ := rfl

@[simp] theorem rawConstantPullback_app (U : Opens Y) :
    (rawConstantPullback f A).app (op U) = 𝟙 A := rfl

@[simp] theorem rawConstantPullback_app_apply (U : Opens Y) (a : A) :
    (rawConstantPullback f A).app (op U) a = a := rfl

/-- The actual constant augmentation is natural for the native raw
presheaf pullback, not only for its later cohomology classes. -/
@[reassoc] theorem rawPullback_constantAugmentation :
    constantAugmentation Y A ≫ rawPullback f A 0 =
      rawConstantPullback f A ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} f).map
          (constantAugmentation X A) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact singularPullback_constant A (preimageMap f U.unop) a

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
