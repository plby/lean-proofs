import Mathlib.Topology.Germ
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Complex.Basic

/-!
# Rings of actual analytic germs

An analytic germ is an actual neighbourhood germ of complex-valued
functions admitting an analytic representative. Addition and multiplication
come from the usual germ ring. Evaluation is the common value of all
representatives, and analytic pullback is actual composition of germs.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

section FilterComposition

variable {X Y Z : Type*} {l : Filter Y} {lc : Filter X} {ld : Filter Z}

/-- Actual composition of complex-valued filter germs, as a ring map. -/
def compTendstoRingHom (g : X → Y) (hg : Tendsto g lc l) :
    Filter.Germ l ℂ →+* Filter.Germ lc ℂ where
  toFun φ := φ.compTendsto g hg
  map_zero' := rfl
  map_one' := rfl
  map_add' φ ψ := Filter.Germ.inductionOn₂ φ ψ (fun _ _ => rfl)
  map_mul' φ ψ := Filter.Germ.inductionOn₂ φ ψ (fun _ _ => rfl)

@[simp] theorem compTendstoRingHom_apply (g : X → Y) (hg : Tendsto g lc l)
    (φ : Filter.Germ l ℂ) : compTendstoRingHom g hg φ = φ.compTendsto g hg := rfl

@[simp] theorem compTendstoRingHom_ofFun (g : X → Y) (hg : Tendsto g lc l)
    (f : Y → ℂ) :
    compTendstoRingHom g hg (f : Filter.Germ l ℂ) =
      ((f ∘ g) : Filter.Germ lc ℂ) := rfl

@[simp] theorem compTendstoRingHom_id (l : Filter X) :
    compTendstoRingHom (id : X → X) (tendsto_id : Tendsto id l l) =
      RingHom.id (Filter.Germ l ℂ) := by
  apply RingHom.ext
  intro φ
  exact Filter.Germ.inductionOn φ (fun _ => rfl)

theorem compTendstoRingHom_comp (g : X → Y) (hg : Tendsto g lc l)
    (h : Y → Z) (hh : Tendsto h l ld) :
    compTendstoRingHom (h ∘ g) (hh.comp hg) =
      (compTendstoRingHom g hg).comp (compTendstoRingHom h hh) := by
  apply RingHom.ext
  intro φ
  exact Filter.Germ.inductionOn φ (fun _ => rfl)

theorem compTendstoRingHom_congr {g h : X → Y} (hg : Tendsto g lc l)
    (hh : Tendsto h lc l) (he : g =ᶠ[lc] h) :
    compTendstoRingHom g hg = compTendstoRingHom h hh := by
  apply RingHom.ext
  intro φ
  refine Filter.Germ.inductionOn φ fun f => ?_
  exact Filter.Germ.coe_eq.mpr (he.fun_comp f)

end FilterComposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual subring of neighbourhood germs admitting an analytic
representative at the specified point. -/
def analyticSubring (a : E) : Subring (Filter.Germ (𝓝 a) ℂ) where
  carrier := {φ | ∃ f : E → ℂ, AnalyticAt ℂ f a ∧ (f : Filter.Germ (𝓝 a) ℂ) = φ}
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro φ ψ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro φ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- Analytic germs, with the inherited commutative ring operations. -/
abbrev AnalyticGerm (a : E) := ↥(analyticSubring a)

variable {a : E}

/-- The genuine germ of an analytic representative. -/
def ofAnalytic (f : E → ℂ) (hf : AnalyticAt ℂ f a) : AnalyticGerm a :=
  ⟨(f : Filter.Germ (𝓝 a) ℂ), f, hf, rfl⟩

@[simp] theorem coe_ofAnalytic (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    (ofAnalytic f hf : Filter.Germ (𝓝 a) ℂ) = f := rfl

@[ext] theorem ext {φ ψ : AnalyticGerm a}
    (h : (φ : Filter.Germ (𝓝 a) ℂ) = (ψ : Filter.Germ (𝓝 a) ℂ)) : φ = ψ :=
  Subtype.ext h

/-- Equality of analytic germs is exactly equality on some neighbourhood. -/
theorem ofAnalytic_eq_iff (f g : E → ℂ) (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a) :
    ofAnalytic f hf = ofAnalytic g hg ↔ f =ᶠ[𝓝 a] g :=
  Subtype.ext_iff.trans Filter.Germ.coe_eq

theorem exists_representative (φ : AnalyticGerm a) :
    ∃ (f : E → ℂ) (hf : AnalyticAt ℂ f a), ofAnalytic f hf = φ := by
  obtain ⟨f, hf, he⟩ := φ.property
  exact ⟨f, hf, Subtype.ext he⟩

@[simp] theorem ofAnalytic_zero :
    ofAnalytic (fun _ : E => (0 : ℂ)) (analyticAt_const (x := a)) = 0 := rfl

@[simp] theorem ofAnalytic_one :
    ofAnalytic (fun _ : E => (1 : ℂ)) (analyticAt_const (x := a)) = 1 := rfl

@[simp] theorem ofAnalytic_add (f g : E → ℂ) (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a) :
    ofAnalytic (f + g) (hf.add hg) = ofAnalytic f hf + ofAnalytic g hg := rfl

@[simp] theorem ofAnalytic_mul (f g : E → ℂ) (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a) :
    ofAnalytic (f * g) (hf.mul hg) = ofAnalytic f hf * ofAnalytic g hg := rfl

@[simp] theorem ofAnalytic_neg (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    ofAnalytic (-f) hf.neg = -ofAnalytic f hf := rfl

@[simp] theorem ofAnalytic_sub (f g : E → ℂ) (hf : AnalyticAt ℂ f a)
    (hg : AnalyticAt ℂ g a) :
    ofAnalytic (f - g) (hf.sub hg) = ofAnalytic f hf - ofAnalytic g hg := rfl

/-- Evaluation is inherited from the actual neighbourhood-germ ring map. -/
def eval (a : E) : AnalyticGerm a →+* ℂ :=
  (Filter.Germ.valueRingHom (x := a) : Filter.Germ (𝓝 a) ℂ →+* ℂ).comp
    (analyticSubring a).subtype

@[simp] theorem eval_ofAnalytic (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    eval a (ofAnalytic f hf) = f a := rfl

/-- Constant analytic functions give the actual constant germs. -/
def constant (a : E) : ℂ →+* AnalyticGerm a where
  toFun c := ofAnalytic (fun _ => c) analyticAt_const
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem eval_constant (a : E) (c : ℂ) : eval a (constant a c) = c := rfl

theorem constant_injective (a : E) : Function.Injective (constant a) :=
  (show Function.LeftInverse (eval a) (constant a) from fun _ => rfl).injective

theorem eval_surjective (a : E) : Function.Surjective (eval a) :=
  fun c => ⟨constant a c, rfl⟩

section Pullback

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Analytic pullback is the restriction of actual germ composition to the
analytic subrings. -/
def pullback (g : E → F) (hg : AnalyticAt ℂ g a) :
    AnalyticGerm (g a) →+* AnalyticGerm a :=
  ((compTendstoRingHom g hg.continuousAt).comp (analyticSubring (g a)).subtype).codRestrict
    (analyticSubring a) (by
      intro φ
      obtain ⟨f, hf, he⟩ := φ.property
      refine ⟨f ∘ g, hf.comp hg, ?_⟩
      change ((f ∘ g) : Filter.Germ (𝓝 a) ℂ) =
        (φ : Filter.Germ (𝓝 (g a)) ℂ).compTendsto g hg.continuousAt
      rw [← he]
      rfl)

@[simp] theorem pullback_ofAnalytic (g : E → F) (hg : AnalyticAt ℂ g a)
    (f : F → ℂ) (hf : AnalyticAt ℂ f (g a)) :
    pullback g hg (ofAnalytic f hf) = ofAnalytic (f ∘ g) (hf.comp hg) := rfl

@[simp] theorem coe_pullback (g : E → F) (hg : AnalyticAt ℂ g a)
    (φ : AnalyticGerm (g a)) :
    (pullback g hg φ : Filter.Germ (𝓝 a) ℂ) =
      compTendstoRingHom g hg.continuousAt (φ : Filter.Germ (𝓝 (g a)) ℂ) := rfl

@[simp] theorem pullback_id (a : E) :
    pullback (id : E → E) (analyticAt_id (z := a)) = RingHom.id (AnalyticGerm a) := by
  apply RingHom.ext
  intro φ
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rfl

theorem pullback_comp (g : E → F) (hg : AnalyticAt ℂ g a)
    (h : F → G) (hh : AnalyticAt ℂ h (g a)) :
    pullback (h ∘ g) (hh.comp hg) = (pullback g hg).comp (pullback h hh) := by
  apply RingHom.ext
  intro φ
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rfl

@[simp] theorem eval_pullback (g : E → F) (hg : AnalyticAt ℂ g a)
    (φ : AnalyticGerm (g a)) : eval a (pullback g hg φ) = eval (g a) φ := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rfl

/-- The same actual pullback with an explicitly named target point. -/
def pullbackAt {b : F} (g : E → F) (hg : AnalyticAt ℂ g a) (hab : g a = b) :
    AnalyticGerm b →+* AnalyticGerm a := by
  subst b
  exact pullback g hg

@[simp] theorem pullbackAt_ofAnalytic {b : F} (g : E → F) (hg : AnalyticAt ℂ g a)
    (hab : g a = b) (f : F → ℂ) (hf : AnalyticAt ℂ f b) :
    pullbackAt g hg hab (ofAnalytic f hf) = ofAnalytic (f ∘ g) (hf.comp_of_eq hg hab) := by
  subst b
  rfl

@[simp] theorem coe_pullbackAt {b : F} (g : E → F) (hg : AnalyticAt ℂ g a)
    (hab : g a = b) (φ : AnalyticGerm b) :
    (pullbackAt g hg hab φ : Filter.Germ (𝓝 a) ℂ) =
      compTendstoRingHom g (show Tendsto g (𝓝 a) (𝓝 b) from
        hab ▸ hg.continuousAt) (φ : Filter.Germ (𝓝 b) ℂ) := by
  subst b
  rfl

@[simp] theorem pullbackAt_rfl (g : E → F) (hg : AnalyticAt ℂ g a) :
    pullbackAt g hg rfl = pullback g hg := rfl

@[simp] theorem eval_pullbackAt {b : F} (g : E → F) (hg : AnalyticAt ℂ g a)
    (hab : g a = b) (φ : AnalyticGerm b) : eval a (pullbackAt g hg hab φ) = eval b φ := by
  subst b
  exact eval_pullback g hg φ

theorem pullbackAt_comp {b : F} {c : G} (g : E → F) (hg : AnalyticAt ℂ g a)
    (hab : g a = b) (h : F → G) (hh : AnalyticAt ℂ h b) (hbc : h b = c) :
    pullbackAt (h ∘ g) (hh.comp_of_eq hg hab) ((congrArg h hab).trans hbc) =
      (pullbackAt g hg hab).comp (pullbackAt h hh hbc) := by
  subst b
  subst c
  exact pullback_comp g hg h hh

theorem pullbackAt_congr {b : F} {g h : E → F} (hg : AnalyticAt ℂ g a)
    (hh : AnalyticAt ℂ h a) (hga : g a = b) (hha : h a = b)
    (he : g =ᶠ[𝓝 a] h) : pullbackAt g hg hga = pullbackAt h hh hha := by
  apply RingHom.ext
  intro φ
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rw [pullbackAt_ofAnalytic, pullbackAt_ofAnalytic]
  exact (ofAnalytic_eq_iff _ _ _ _).mpr (he.fun_comp f)

end Pullback

end Wikipedia.HopfProblem.CuspNormalization.Germs
