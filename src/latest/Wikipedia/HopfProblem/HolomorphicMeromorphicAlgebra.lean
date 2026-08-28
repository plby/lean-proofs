import Wikipedia.HopfProblem.HolomorphicMeromorphicSections

/-!
# Pointwise algebra of genuine local meromorphic functions

The local-fraction predicate is preserved by addition, multiplication,
and negation. Local presentations are restricted to the intersection
of their actual neighborhoods before the fraction formulas are applied.
Thus genuine locally meromorphic sections form a commutative ring with
pointwise operations, and literal restriction is a ring homomorphism.
-/

noncomputable section

open Set Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

theorem isFraction_zero (U : Opens M) :
    IsFraction I M (fun x : U => (0 : Germ I M x.val)) := by
  refine ⟨0, 1, ?_, ?_⟩
  · intro x
    rw [map_one]
    exact one_ne_zero
  · intro x
    simp only [fraction, map_zero, map_one, zero_div]

theorem isFraction_one (U : Opens M) :
    IsFraction I M (fun x : U => (1 : Germ I M x.val)) := by
  refine ⟨1, 1, ?_, ?_⟩
  · intro x
    rw [map_one]
    exact one_ne_zero
  · intro x
    simp only [fraction, map_one, div_one]

theorem isFraction_neg {U : Opens M} {f : ∀ x : U, Germ I M x.val}
    (hf : IsFraction I M f) : IsFraction I M (fun x => -f x) := by
  obtain ⟨p, q, hq, hf⟩ := hf
  refine ⟨-p, q, hq, ?_⟩
  intro x
  change -f x = _
  rw [hf x]
  simp only [fraction, map_neg, neg_div]

theorem isFraction_add {U : Opens M} {f g : ∀ x : U, Germ I M x.val}
    (hf : IsFraction I M f) (hg : IsFraction I M g) :
    IsFraction I M (fun x => f x + g x) := by
  obtain ⟨p, q, hq, hf⟩ := hf
  obtain ⟨r, s, hs, hg⟩ := hg
  refine ⟨p * s + q * r, q * s, ?_, ?_⟩
  · intro x
    rw [map_mul]
    exact mul_ne_zero (hq x) (hs x)
  · intro x
    have hq' : sectionGerm I M U x q ≠ 0 :=
      fun h => hq x ((sectionGerm_eq_zero_iff I M U x q).mp h)
    have hs' : sectionGerm I M U x s ≠ 0 :=
      fun h => hs x ((sectionGerm_eq_zero_iff I M U x s).mp h)
    change f x + g x = _
    rw [hf x, hg x]
    simp only [fraction, map_add, map_mul]
    exact div_add_div _ _ hq' hs'

theorem isFraction_mul {U : Opens M} {f g : ∀ x : U, Germ I M x.val}
    (hf : IsFraction I M f) (hg : IsFraction I M g) :
    IsFraction I M (fun x => f x * g x) := by
  obtain ⟨p, q, hq, hf⟩ := hf
  obtain ⟨r, s, hs, hg⟩ := hg
  refine ⟨p * r, q * s, ?_, ?_⟩
  · intro x
    rw [map_mul]
    exact mul_ne_zero (hq x) (hs x)
  · intro x
    change f x * g x = _
    rw [hf x, hg x]
    simp only [fraction, map_mul, div_mul_div_comm]

theorem localPredicate_zero (U : Opens M) :
    (localPredicate I M).pred (fun x : U => (0 : Germ I M x.val)) :=
  (fractionPrelocal I M).sheafifyOf (isFraction_zero I M U)

theorem localPredicate_one (U : Opens M) :
    (localPredicate I M).pred (fun x : U => (1 : Germ I M x.val)) :=
  (fractionPrelocal I M).sheafifyOf (isFraction_one I M U)

theorem localPredicate_neg {U : Opens M} {f : ∀ x : U, Germ I M x.val}
    (hf : (localPredicate I M).pred f) :
    (localPredicate I M).pred (fun x => -f x) :=
  (fractionPrelocal I M).sheafify_inductionOn' (fun {_} a => -a)
    (fun h => isFraction_neg I M h) hf

theorem localPredicate_add {U : Opens M} {f g : ∀ x : U, Germ I M x.val}
    (hf : (localPredicate I M).pred f) (hg : (localPredicate I M).pred g) :
    (localPredicate I M).pred (fun x => f x + g x) := by
  refine (fractionPrelocal I M).sheafify_inductionOn₂'
    (fractionPrelocal I M) (fractionPrelocal I M) (fun {_} a b => a + b) ?_ hf hg
  intro V W a b ha hb
  exact isFraction_add I M
    ((fractionPrelocal I M).res (Opens.infLELeft V W) a ha)
    ((fractionPrelocal I M).res (Opens.infLERight V W) b hb)

theorem localPredicate_mul {U : Opens M} {f g : ∀ x : U, Germ I M x.val}
    (hf : (localPredicate I M).pred f) (hg : (localPredicate I M).pred g) :
    (localPredicate I M).pred (fun x => f x * g x) := by
  refine (fractionPrelocal I M).sheafify_inductionOn₂'
    (fractionPrelocal I M) (fractionPrelocal I M) (fun {_} a b => a * b) ?_ hf hg
  intro V W a b ha hb
  exact isFraction_mul I M
    ((fractionPrelocal I M).res (Opens.infLELeft V W) a ha)
    ((fractionPrelocal I M).res (Opens.infLERight V W) b hb)

/-- Locally represented fractions form a subring of the dependent product
of genuine meromorphic germ fields. -/
def sectionSubring (U : Opens M) : Subring (∀ x : U, Germ I M x.val) where
  carrier := {f | (localPredicate I M).pred f}
  zero_mem' := localPredicate_zero I M U
  one_mem' := localPredicate_one I M U
  add_mem' := fun hf hg => localPredicate_add I M hf hg
  neg_mem' := fun hf => localPredicate_neg I M hf
  mul_mem' := fun hf hg => localPredicate_mul I M hf hg

/-- The ring operations are the actual pointwise germ-field operations. -/
instance section_commRing (U : Opens M) : CommRing (Section I M U) :=
  (sectionSubring I M U).toCommRing

@[simp] theorem section_zero_apply (U : Opens M) (x : U) :
    (0 : Section I M U) x = 0 := rfl

@[simp] theorem section_one_apply (U : Opens M) (x : U) :
    (1 : Section I M U) x = 1 := rfl

@[simp] theorem section_add_apply {U : Opens M} (f g : Section I M U) (x : U) :
    (f + g) x = f x + g x := rfl

@[simp] theorem section_neg_apply {U : Opens M} (f : Section I M U) (x : U) :
    (-f) x = -f x := rfl

@[simp] theorem section_sub_apply {U : Opens M} (f g : Section I M U) (x : U) :
    (f - g) x = f x - g x := rfl

@[simp] theorem section_mul_apply {U : Opens M} (f g : Section I M U) (x : U) :
    (f * g) x = f x * g x := rfl

/-- Evaluation is a homomorphism into the genuine meromorphic germ field. -/
def evalRingHom (U : Opens M) (x : U) : Section I M U →+* Germ I M x.val where
  toFun f := f x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem evalRingHom_apply (U : Opens M) (x : U) (f : Section I M U) :
    evalRingHom I M U x f = f x := rfl

/-- Literal restriction preserves the pointwise ring operations. -/
def restrictionRingHom {U V : Opens M} (h : U ≤ V) :
    Section I M V →+* Section I M U where
  toFun := restrict I M h
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem restrictionRingHom_apply {U V : Opens M} (h : U ≤ V)
    (f : Section I M V) : restrictionRingHom I M h f = restrict I M h f := rfl

/-- The canonical inclusion of actual holomorphic functions is a ring homomorphism. -/
def ofHolomorphicRingHom (U : Opens M) :
    HolomorphicFunctionSheaf.Section I M U →+* Section I M U where
  toFun := ofHolomorphic I M U
  map_zero' := by
    ext x
    simp only [ofHolomorphic_apply, map_zero, section_zero_apply]
  map_one' := by
    ext x
    simp only [ofHolomorphic_apply, map_one, section_one_apply]
  map_add' f g := by
    ext x
    simp only [ofHolomorphic_apply, map_add, section_add_apply]
  map_mul' f g := by
    ext x
    simp only [ofHolomorphic_apply, map_mul, section_mul_apply]

@[simp] theorem ofHolomorphicRingHom_apply (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    ofHolomorphicRingHom I M U f = ofHolomorphic I M U f := rfl

theorem ofHolomorphicRingHom_injective (U : Opens M) :
    Function.Injective (ofHolomorphicRingHom I M U) :=
  ofHolomorphic_injective I M U

@[simp] theorem ofHolomorphic_restrict {U V : Opens M} (h : U ≤ V)
    (f : HolomorphicFunctionSheaf.Section I M V) :
    ofHolomorphic I M U (HolomorphicFunctionSheaf.restrictionAlgHom I M h f) =
      restrict I M h (ofHolomorphic I M V f) := by
  ext x
  simp only [ofHolomorphic_apply, sectionGerm_restrict, restrict_apply]

/-- The inclusion commutes with actual restriction as an equality of ring maps. -/
theorem ofHolomorphicRingHom_restriction {U V : Opens M} (h : U ≤ V) :
    (ofHolomorphicRingHom I M U).comp
        (HolomorphicFunctionSheaf.restrictionAlgHom I M h).toRingHom =
      (restrictionRingHom I M h).comp (ofHolomorphicRingHom I M V) := by
  apply RingHom.ext
  intro f
  exact ofHolomorphic_restrict I M h f

end Wikipedia.HopfProblem.HolomorphicMeromorphic
