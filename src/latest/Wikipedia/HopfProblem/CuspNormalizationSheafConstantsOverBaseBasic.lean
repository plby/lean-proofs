import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsPullback

/-!
# Actual constant-sheaf pullback over a common base

The map on a base open set is the actual constant-sheaf pullback on its
inverse image, followed by literal restriction to the other inverse
image.  The same construction applies to any sheaf pullback and
preserves commuting squares of the original sheaf maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {X Y B : TopCat.{0}} (p : Y ⟶ B) (q : X ⟶ B) (f : X ⟶ Y)
  (hf : ∀ x : X, p (f x) = q x)

include hf

/-- The actual inclusion between inverse-image opens coming from the
given equality of the two maps to the base. -/
theorem overBasePreimageLE (U : Opens B) :
    (Opens.map q).obj U ≤ (Opens.map f).obj ((Opens.map p).obj U) := by
  intro x hx
  change p (f x) ∈ U
  rw [hf]
  exact hx

/-- Push an actual sheaf pullback to the common base, using literal
restriction between the actual inverse-image opens. -/
def pushforwardOverBaseMap (FX : TopCat.Sheaf CommRingCat X) (FY : TopCat.Sheaf CommRingCat Y)
    (φ : FY ⟶ (TopCat.Sheaf.pushforward CommRingCat f).obj FX) :
    (TopCat.Sheaf.pushforward CommRingCat p).obj FY ⟶
      (TopCat.Sheaf.pushforward CommRingCat q).obj FX :=
  ObjectProperty.homMk
    { app U := φ.hom.app (op ((Opens.map p).obj U.unop)) ≫
        FX.obj.map (homOfLE (overBasePreimageLE p q f hf U.unop)).op
      naturality U V h := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro s
        let k := ((Opens.map p).map h.unop).op
        let kf := ((Opens.map f).map ((Opens.map p).map h.unop)).op
        let kq := ((Opens.map q).map h.unop).op
        let aU := (homOfLE (overBasePreimageLE p q f hf U.unop)).op
        let aV := (homOfLE (overBasePreimageLE p q f hf V.unop)).op
        let t := φ.hom.app (op ((Opens.map p).obj U.unop)) s
        have hn := ConcreteCategory.congr_hom (φ.hom.naturality k) s
        have he : kf ≫ aV = aU ≫ kq := Subsingleton.elim _ _
        have h₁ := ConcreteCategory.congr_hom (FX.obj.map_comp kf aV) t
        have h₂ := ConcreteCategory.congr_hom (FX.obj.map_comp aU kq) t
        exact (congrArg (FX.obj.map aV) hn).trans
          (h₁.symm.trans ((congrArg (fun k' => FX.obj.map k' t) he).trans h₂)) }

@[simp] theorem pushforwardOverBaseMap_app
    (FX : TopCat.Sheaf CommRingCat X) (FY : TopCat.Sheaf CommRingCat Y)
    (φ : FY ⟶ (TopCat.Sheaf.pushforward CommRingCat f).obj FX) (U : Opens B) :
    (pushforwardOverBaseMap p q f hf FX FY φ).hom.app (op U) =
      φ.hom.app (op ((Opens.map p).obj U)) ≫
        FX.obj.map (homOfLE (overBasePreimageLE p q f hf U)).op := rfl

/-- Commuting actual pullback squares remain commuting after putting
all sheaves over the common base. -/
theorem pushforwardOverBaseMap_naturality
    {FX₁ FX₂ : TopCat.Sheaf CommRingCat X} {FY₁ FY₂ : TopCat.Sheaf CommRingCat Y}
    (φ₁ : FY₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat f).obj FX₁)
    (φ₂ : FY₂ ⟶ (TopCat.Sheaf.pushforward CommRingCat f).obj FX₂)
    (α : FY₁ ⟶ FY₂) (β : FX₁ ⟶ FX₂)
    (h : α ≫ φ₂ = φ₁ ≫ (TopCat.Sheaf.pushforward CommRingCat f).map β) :
    (TopCat.Sheaf.pushforward CommRingCat p).map α ≫
        pushforwardOverBaseMap p q f hf FX₂ FY₂ φ₂ =
      pushforwardOverBaseMap p q f hf FX₁ FY₁ φ₁ ≫
        (TopCat.Sheaf.pushforward CommRingCat q).map β := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  let aU := (homOfLE (overBasePreimageLE p q f hf U.unop)).op
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun k => k.hom) h)
      (op ((Opens.map p).obj U.unop))) s
  have hβ := ConcreteCategory.congr_hom (β.hom.naturality aU)
    (φ₁.hom.app (op ((Opens.map p).obj U.unop)) s)
  exact (congrArg (FX₂.obj.map aU) hn).trans hβ.symm

/-- The actual map between the two pushed-forward constant complex
sheaves over a common base. -/
def overBaseMap :
    (TopCat.Sheaf.pushforward CommRingCat p).obj (complexSheaf Y) ⟶
      (TopCat.Sheaf.pushforward CommRingCat q).obj (complexSheaf X) :=
  pushforwardOverBaseMap p q f hf (complexSheaf X) (complexSheaf Y) (pullbackMap f)

/-- A constant representative retains its value on the actual inverse
image under the over-base map. -/
@[simp] theorem overBaseMap_unit (U : Opens B) (c : ℂ) :
    (overBaseMap p q f hf).hom.app (op U)
        ((unit Y).app (op ((Opens.map p).obj U)) c) =
      (unit X).app (op ((Opens.map q).obj U)) c := by
  change (complexSheaf X).obj.map (homOfLE (overBasePreimageLE p q f hf U)).op
    ((pullbackMap f).hom.app (op ((Opens.map p).obj U))
      ((unit Y).app (op ((Opens.map p).obj U)) c)) = _
  exact (congrArg ((complexSheaf X).obj.map
      (homOfLE (overBasePreimageLE p q f hf U)).op)
    (pullbackMap_unit f ((Opens.map p).obj U) c)).trans
      (ConcreteCategory.congr_hom
        ((unit X).naturality (homOfLE (overBasePreimageLE p q f hf U)).op) c).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
