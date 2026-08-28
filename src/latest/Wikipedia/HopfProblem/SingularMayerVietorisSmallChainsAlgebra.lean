import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The algebraic short exact sequence for a two-set chain cover

The maps into a categorical biproduct are `(a, -b)` and the map out is `(u, v)`.
The intersection-lifting and joint-surjectivity hypotheses are expressed on actual elements.
No injectivity assumption on `u` or `v` is needed once intersection lifting is available.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SmallChainBiprod

variable {A B I S : ModuleCat.{0} ℤ}

theorem fst_lift_apply (a : I ⟶ A) (b : I ⟶ B) (z : I) :
    (biprod.fst : A ⊞ B ⟶ A).hom ((biprod.lift a b).hom z) = a.hom z := by
  exact congrArg (fun f : I ⟶ A => f.hom z) (biprod.lift_fst a b)

theorem snd_lift_apply (a : I ⟶ A) (b : I ⟶ B) (z : I) :
    (biprod.snd : A ⊞ B ⟶ B).hom ((biprod.lift a b).hom z) = b.hom z := by
  exact congrArg (fun f : I ⟶ B => f.hom z) (biprod.lift_snd a b)

theorem desc_inl_apply (u : A ⟶ S) (v : B ⟶ S) (x : A) :
    (biprod.desc u v).hom ((biprod.inl : A ⟶ A ⊞ B).hom x) = u.hom x := by
  exact congrArg (fun f : A ⟶ S => f.hom x) (biprod.inl_desc u v)

theorem desc_inr_apply (u : A ⟶ S) (v : B ⟶ S) (y : B) :
    (biprod.desc u v).hom ((biprod.inr : B ⟶ A ⊞ B).hom y) = v.hom y := by
  exact congrArg (fun f : B ⟶ S => f.hom y) (biprod.inr_desc u v)

theorem total_apply (z : (A ⊞ B : ModuleCat ℤ)) :
    (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom z) +
      (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom z) = z := by
  exact congrArg (fun f : A ⊞ B ⟶ A ⊞ B => f.hom z) biprod.total

theorem element_ext {z z' : (A ⊞ B : ModuleCat ℤ)}
    (hfst : (biprod.fst : A ⊞ B ⟶ A).hom z = (biprod.fst : A ⊞ B ⟶ A).hom z')
    (hsnd : (biprod.snd : A ⊞ B ⟶ B).hom z = (biprod.snd : A ⊞ B ⟶ B).hom z') : z = z' := by
  calc
    z = (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom z) +
        (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom z) :=
      (total_apply z).symm
    _ = (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom z') +
        (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom z') :=
      by rw [hfst, hsnd]
    _ = z' := total_apply z'

theorem desc_apply (u : A ⟶ S) (v : B ⟶ S) (z : (A ⊞ B : ModuleCat ℤ)) :
    (biprod.desc u v).hom z =
      u.hom ((biprod.fst : A ⊞ B ⟶ A).hom z) +
      v.hom ((biprod.snd : A ⊞ B ⟶ B).hom z) := by
  calc
    (biprod.desc u v).hom z =
        (biprod.desc u v).hom
          ((biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom z) +
            (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom z)) :=
      congrArg (biprod.desc u v).hom (total_apply z).symm
    _ = _ := by rw [map_add, desc_inl_apply, desc_inr_apply]

/-- The categorical complex `I → A ⊞ B → S`, with the usual difference and sum maps. -/
def shortComplex (a : I ⟶ A) (b : I ⟶ B) (u : A ⟶ S) (v : B ⟶ S)
    (w : a ≫ u = b ≫ v) : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk (biprod.lift a (-b)) (biprod.desc u v) (by
    rw [biprod.lift_desc, Preadditive.neg_comp, w, add_neg_cancel])

theorem left_injective (a : I ⟶ A) (b : I ⟶ B) (ha : Function.Injective a.hom) :
    Function.Injective (biprod.lift a (-b)).hom := by
  intro z z' h
  apply ha
  have hf := congrArg (biprod.fst : A ⊞ B ⟶ A).hom h
  simpa only [fst_lift_apply] using hf

theorem right_surjective (u : A ⟶ S) (v : B ⟶ S)
    (hjoint : ∀ s : S, ∃ x : A, ∃ y : B, u.hom x + v.hom y = s) :
    Function.Surjective (biprod.desc u v).hom := by
  intro s
  obtain ⟨x, y, hxy⟩ := hjoint s
  refine ⟨(biprod.inl : A ⟶ A ⊞ B).hom x +
    (biprod.inr : B ⟶ A ⊞ B).hom y, ?_⟩
  simpa only [map_add, desc_inl_apply, desc_inr_apply] using hxy

/-- An element in the kernel of the sum map lifts from the common intersection. -/
theorem exact (a : I ⟶ A) (b : I ⟶ B) (u : A ⟶ S) (v : B ⟶ S)
    (w : a ≫ u = b ≫ v)
    (hoverlap : ∀ (x : A) (y : B), u.hom x = v.hom y →
      ∃ z : I, a.hom z = x ∧ b.hom z = y) :
    (shortComplex a b u v w).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro q hq
  change (biprod.desc u v).hom q = 0 at hq
  have hsum : u.hom ((biprod.fst : A ⊞ B ⟶ A).hom q) +
      v.hom ((biprod.snd : A ⊞ B ⟶ B).hom q) = 0 :=
    (desc_apply u v q).symm.trans hq
  have heq : u.hom ((biprod.fst : A ⊞ B ⟶ A).hom q) =
      v.hom (-(biprod.snd : A ⊞ B ⟶ B).hom q) := by
    rw [map_neg]
    exact eq_neg_iff_add_eq_zero.mpr hsum
  obtain ⟨z, haz, hbz⟩ := hoverlap _ _ heq
  refine ⟨z, ?_⟩
  change (biprod.lift a (-b)).hom z = q
  apply element_ext
  · simpa only [fst_lift_apply] using haz
  · rw [snd_lift_apply]
    change -b.hom z = (biprod.snd : A ⊞ B ⟶ B).hom q
    rw [hbz, neg_neg]

/-- The chain-cover algebraic criterion for short exactness. -/
theorem shortExact (a : I ⟶ A) (b : I ⟶ B) (u : A ⟶ S) (v : B ⟶ S)
    (w : a ≫ u = b ≫ v) (ha : Function.Injective a.hom)
    (hjoint : ∀ s : S, ∃ x : A, ∃ y : B, u.hom x + v.hom y = s)
    (hoverlap : ∀ (x : A) (y : B), u.hom x = v.hom y →
      ∃ z : I, a.hom z = x ∧ b.hom z = y) :
    (shortComplex a b u v w).ShortExact where
  exact := exact a b u v w hoverlap
  mono_f := (ModuleCat.mono_iff_injective _).mpr (left_injective a b ha)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (right_surjective u v hjoint)

/-- The same criterion for a short complex formed with an arbitrary proof of zero composition. -/
theorem shortExact_mk (a : I ⟶ A) (b : I ⟶ B) (u : A ⟶ S) (v : B ⟶ S)
    (w : a ≫ u = b ≫ v)
    (hzero : biprod.lift a (-b) ≫ biprod.desc u v = 0)
    (ha : Function.Injective a.hom)
    (hjoint : ∀ s : S, ∃ x : A, ∃ y : B, u.hom x + v.hom y = s)
    (hoverlap : ∀ (x : A) (y : B), u.hom x = v.hom y →
      ∃ z : I, a.hom z = x ∧ b.hom z = y) :
    (ShortComplex.mk (biprod.lift a (-b)) (biprod.desc u v) hzero).ShortExact :=
  shortExact a b u v w ha hjoint hoverlap

section Complexes

variable {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Evaluation of a categorical lift, with the canonical biproduct comparison. -/
theorem lift_f_biprodXIso_hom (a : J ⟶ K) (b : J ⟶ L) (n : ℕ) :
    (biprod.lift a b).f n ≫ (HomologicalComplex.biprodXIso K L n).hom =
      biprod.lift (a.f n) (b.f n) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      HomologicalComplex.biprod_lift_fst_f, biprod.lift_fst]
  · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      HomologicalComplex.biprod_lift_snd_f, biprod.lift_snd]

/-- Evaluation of a categorical descent, with the inverse biproduct comparison. -/
theorem biprodXIso_inv_desc_f (u : K ⟶ T) (v : L ⟶ T) (n : ℕ) :
    (HomologicalComplex.biprodXIso K L n).inv ≫ (biprod.desc u v).f n =
      biprod.desc (u.f n) (v.f n) := by
  apply biprod.hom_ext'
  · simp only [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
      HomologicalComplex.biprod_inl_desc_f, biprod.inl_desc]
  · simp only [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
      HomologicalComplex.biprod_inr_desc_f, biprod.inr_desc]

/-- Evaluation of descent, expressed using the forward biproduct comparison. -/
theorem biprodXIso_hom_desc_f (u : K ⟶ T) (v : L ⟶ T) (n : ℕ) :
    (HomologicalComplex.biprodXIso K L n).hom ≫ biprod.desc (u.f n) (v.f n) =
      (biprod.desc u v).f n := by
  rw [← biprodXIso_inv_desc_f u v n, Iso.hom_inv_id_assoc]

/-- The difference-sum short complex in the category of chain complexes. -/
def shortComplexOfComplexes (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T)
    (w : a ≫ u = b ≫ v) : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (biprod.lift a (-b)) (biprod.desc u v) (by
    rw [biprod.lift_desc, Preadditive.neg_comp, w, add_neg_cancel])

/-- The degreewise square obtained from a commuting square of chain maps. -/
theorem square_f (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T)
    (w : a ≫ u = b ≫ v) (n : ℕ) :
    a.f n ≫ u.f n = b.f n ≫ v.f n :=
  congrArg (fun f : J ⟶ T => f.f n) w

/-- Evaluation of the chain-level short complex is the module-level short complex,
via the actual categorical biproduct comparison in the middle. -/
def shortComplexOfComplexesEvalIso
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T)
    (w : a ≫ u = b ≫ v) (n : ℕ) :
    (shortComplexOfComplexes a b u v w).map
        (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) ≅
      shortComplex (a.f n) (b.f n) (u.f n) (v.f n) (square_f a b u v w n) := by
  refine ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.biprodXIso K L n)
    (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ biprod.lift (a.f n) (-(b.f n)) =
      (biprod.lift a (-b)).f n ≫ (HomologicalComplex.biprodXIso K L n).hom
    simpa only [Category.id_comp, HomologicalComplex.neg_f_apply] using
      (lift_f_biprodXIso_hom a (-b) n).symm
  · change (HomologicalComplex.biprodXIso K L n).hom ≫
        biprod.desc (u.f n) (v.f n) = (biprod.desc u v).f n ≫ 𝟙 _
    simpa only [Category.comp_id] using biprodXIso_hom_desc_f u v n

/-- Degreewise intersection lifting and joint surjectivity produce an actual short exact
sequence of chain complexes. -/
theorem shortExactOfComplexes
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T)
    (w : a ≫ u = b ≫ v)
    (ha : ∀ n : ℕ, Function.Injective (a.f n).hom)
    (hjoint : ∀ (n : ℕ) (s : T.X n), ∃ x : K.X n, ∃ y : L.X n,
      (u.f n).hom x + (v.f n).hom y = s)
    (hoverlap : ∀ (n : ℕ) (x : K.X n) (y : L.X n),
      (u.f n).hom x = (v.f n).hom y →
        ∃ z : J.X n, (a.f n).hom z = x ∧ (b.f n).hom z = y) :
    (shortComplexOfComplexes a b u v w).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact ShortComplex.shortExact_of_iso (shortComplexOfComplexesEvalIso a b u v w n).symm
    (shortExact (a.f n) (b.f n) (u.f n) (v.f n) (square_f a b u v w n)
      (ha n) (hjoint n) (hoverlap n))

end Complexes

end Wikipedia.HopfProblem.SmallChainBiprod
