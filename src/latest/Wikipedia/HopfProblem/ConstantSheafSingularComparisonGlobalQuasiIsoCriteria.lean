import Wikipedia.HopfProblem.SheafHigherDirectImageExtBasic
import Mathlib.Algebra.Homology.QuasiIso

/-!
# A native cohomology-isomorphism criterion from actual cocycle lifts

Exact lifts of closed representatives make the original homology map
surjective.  Detection of actual boundaries makes it injective.  The proof
uses the original categorical homology and its canonical kernel-quotient
comparison, including the native cycle-class and homology-map formulas.

The positive-degree criterion is stated using literal consecutive
differentials, so it applies directly to degrees one and two of genuine
cochain complexes of abelian groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.GlobalQuasiIsoCriteria

open SheafHigherDirectImage.ExtBridge

section ShortComplex

/-- The original cycle class maps to its actual kernel-quotient representative. -/
theorem shortCycleClass_quotient (S : ShortComplex AddCommGrpCat.{0})
    (z : S.X₂) (hz : S.g z = 0) :
    S.abHomologyIso.hom (shortCycleClass S z hz) =
      QuotientAddGroup.mk' S.abToCycles.range ⟨z, hz⟩ := by
  have h : S.abCyclesIso.inv ≫ S.homologyπ ≫ S.abHomologyIso.hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' S.abToCycles.range) := by
    change S.abLeftHomologyData.cyclesIso.inv ≫ S.homologyπ ≫
      S.abLeftHomologyData.homologyIso.hom = S.abLeftHomologyData.π
    rw [S.abLeftHomologyData.homologyπ_comp_homologyIso_hom,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact ConcreteCategory.congr_hom h ⟨z, hz⟩

/-- A native cycle class is zero exactly when its actual representative is a boundary. -/
theorem shortCycleClass_eq_zero_iff (S : ShortComplex AddCommGrpCat.{0})
    (z : S.X₂) (hz : S.g z = 0) :
    shortCycleClass S z hz = 0 ↔ ∃ b : S.X₁, S.f b = z := by
  constructor
  · intro h
    have hq : QuotientAddGroup.mk' S.abToCycles.range ⟨z, hz⟩ = 0 :=
      (shortCycleClass_quotient S z hz).symm.trans
        ((congrArg S.abHomologyIso.hom h).trans S.abHomologyIso.hom.hom.map_zero)
    have hb : (⟨z, hz⟩ : S.g.hom.ker) ∈ S.abToCycles.range :=
      (QuotientAddGroup.eq_zero_iff _).mp hq
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hq : QuotientAddGroup.mk' S.abToCycles.range ⟨z, hz⟩ = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨b, Subtype.ext hb⟩
    apply (AddCommGrpCat.mono_iff_injective S.abHomologyIso.hom).mp inferInstance
    exact ((shortCycleClass_quotient S z hz).trans hq).trans
      S.abHomologyIso.hom.hom.map_zero.symm

variable {S T : ShortComplex AddCommGrpCat.{0}}

/-- Exact lifts of all actual closed representatives give surjectivity on native homology. -/
theorem shortHomologyMap_surjective_of_cycle_lifts (f : S ⟶ T)
    (hlift : ∀ (z : T.X₂), T.g z = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ f.τ₂ x = z) :
    Function.Surjective (ShortComplex.homologyMap f) := by
  intro a
  obtain ⟨z, hz, rfl⟩ := shortCycleClass_surjective T a
  obtain ⟨x, hx, rfl⟩ := hlift z hz
  exact ⟨shortCycleClass S x hx, shortHomologyMap_cycleClass f x hx hz⟩

/-- Detection of boundaries of closed representatives gives injectivity on native homology. -/
theorem shortHomologyMap_injective_of_boundary_detection (f : S ⟶ T)
    (hdetect : ∀ (x : S.X₂), S.g x = 0 →
      (∃ b : T.X₁, T.f b = f.τ₂ x) → ∃ a : S.X₁, S.f a = x) :
    Function.Injective (ShortComplex.homologyMap f) := by
  apply (injective_iff_map_eq_zero (ShortComplex.homologyMap f).hom).mpr
  intro a ha
  obtain ⟨x, hx, rfl⟩ := shortCycleClass_surjective S a
  have hfx : T.g (f.τ₂ x) = 0 :=
    (ConcreteCategory.congr_hom f.comm₂₃ x).trans (by
      change f.τ₃ (S.g x) = 0
      rw [hx]
      exact f.τ₃.hom.map_zero)
  rw [shortHomologyMap_cycleClass f x hx hfx] at ha
  exact (shortCycleClass_eq_zero_iff S x hx).mpr
    (hdetect x hx ((shortCycleClass_eq_zero_iff T (f.τ₂ x) hfx).mp ha))

/-- The criterion produces an isomorphism of the actual native homology objects. -/
theorem isIso_shortHomologyMap_of_cycle_lifts (f : S ⟶ T)
    (hlift : ∀ (z : T.X₂), T.g z = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ f.τ₂ x = z)
    (hdetect : ∀ (x : S.X₂), S.g x = 0 →
      (∃ b : T.X₁, T.f b = f.τ₂ x) → ∃ a : S.X₁, S.f a = x) :
    IsIso (ShortComplex.homologyMap f) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨shortHomologyMap_injective_of_boundary_detection f hdetect,
      shortHomologyMap_surjective_of_cycle_lifts f hlift⟩

end ShortComplex

section CochainComplex

variable {K L : CochainComplex AddCommGrpCat.{0} ℕ}

private theorem sc_closed_iff (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (n : ℕ) (x : K.X (n + 1)) :
    (K.sc (n + 1)).g x = 0 ↔ K.d (n + 1) (n + 2) x = 0 := by
  change K.d (n + 1) ((ComplexShape.up ℕ).next (n + 1)) x = 0 ↔ _
  rw [CochainComplex.next]
  rfl

private theorem sc_boundary_iff (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (n : ℕ) (x : K.X (n + 1)) :
    (∃ a : (K.sc (n + 1)).X₁, (K.sc (n + 1)).f a = x) ↔
      ∃ a : K.X n, K.d n (n + 1) a = x := by
  change (∃ a : K.X ((ComplexShape.up ℕ).prev (n + 1)),
    K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) a = x) ↔ _
  rw [CochainComplex.prev_nat_succ]

/-- Closed lifts in degree `n+1` make the original cohomology map surjective. -/
theorem homologyMap_succ_surjective_of_cycle_lifts (f : K ⟶ L) (n : ℕ)
    (hlift : ∀ (z : L.X (n + 1)), L.d (n + 1) (n + 2) z = 0 →
      ∃ x : K.X (n + 1), K.d (n + 1) (n + 2) x = 0 ∧ f.f (n + 1) x = z) :
    Function.Surjective (HomologicalComplex.homologyMap f (n + 1)) := by
  apply shortHomologyMap_surjective_of_cycle_lifts
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ) (n + 1)).map f)
  intro z hz
  obtain ⟨x, hx, hfx⟩ := hlift z ((sc_closed_iff L n z).mp hz)
  exact ⟨x, (sc_closed_iff K n x).mpr hx, hfx⟩

/-- Actual boundary detection in degree `n+1` makes the native cohomology map injective. -/
theorem homologyMap_succ_injective_of_boundary_detection (f : K ⟶ L) (n : ℕ)
    (hdetect : ∀ (x : K.X (n + 1)), K.d (n + 1) (n + 2) x = 0 →
      (∃ b : L.X n, L.d n (n + 1) b = f.f (n + 1) x) →
        ∃ a : K.X n, K.d n (n + 1) a = x) :
    Function.Injective (HomologicalComplex.homologyMap f (n + 1)) := by
  apply shortHomologyMap_injective_of_boundary_detection
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ) (n + 1)).map f)
  intro x hx hb
  exact (sc_boundary_iff K n x).mpr
    (hdetect x ((sc_closed_iff K n x).mp hx)
      ((sc_boundary_iff L n (f.f (n + 1) x)).mp hb))

/-- Exact lifts of closed cochains and detection of actual boundaries imply
that the original positive-degree homology map is an isomorphism. -/
theorem isIso_homologyMap_succ_of_cycle_lifts (f : K ⟶ L) (n : ℕ)
    (hlift : ∀ (z : L.X (n + 1)), L.d (n + 1) (n + 2) z = 0 →
      ∃ x : K.X (n + 1), K.d (n + 1) (n + 2) x = 0 ∧ f.f (n + 1) x = z)
    (hdetect : ∀ (x : K.X (n + 1)), K.d (n + 1) (n + 2) x = 0 →
      (∃ b : L.X n, L.d n (n + 1) b = f.f (n + 1) x) →
        ∃ a : K.X n, K.d n (n + 1) a = x) :
    IsIso (HomologicalComplex.homologyMap f (n + 1)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨homologyMap_succ_injective_of_boundary_detection f n hdetect,
      homologyMap_succ_surjective_of_cycle_lifts f n hlift⟩

/-- The same result as Mathlib's native positive-degree quasi-isomorphism predicate. -/
theorem quasiIsoAt_succ_of_cycle_lifts (f : K ⟶ L) (n : ℕ)
    (hlift : ∀ (z : L.X (n + 1)), L.d (n + 1) (n + 2) z = 0 →
      ∃ x : K.X (n + 1), K.d (n + 1) (n + 2) x = 0 ∧ f.f (n + 1) x = z)
    (hdetect : ∀ (x : K.X (n + 1)), K.d (n + 1) (n + 2) x = 0 →
      (∃ b : L.X n, L.d n (n + 1) b = f.f (n + 1) x) →
        ∃ a : K.X n, K.d n (n + 1) a = x) :
    QuasiIsoAt f (n + 1) :=
  (quasiIsoAt_iff_isIso_homologyMap f (n + 1)).mpr
    (isIso_homologyMap_succ_of_cycle_lifts f n hlift hdetect)

/-- The native cohomology isomorphism obtained from the proved criterion. -/
def homologyIsoOfCycleLifts (f : K ⟶ L) (n : ℕ)
    (hlift : ∀ (z : L.X (n + 1)), L.d (n + 1) (n + 2) z = 0 →
      ∃ x : K.X (n + 1), K.d (n + 1) (n + 2) x = 0 ∧ f.f (n + 1) x = z)
    (hdetect : ∀ (x : K.X (n + 1)), K.d (n + 1) (n + 2) x = 0 →
      (∃ b : L.X n, L.d n (n + 1) b = f.f (n + 1) x) →
        ∃ a : K.X n, K.d n (n + 1) a = x) :
    K.homology (n + 1) ≅ L.homology (n + 1) := by
  letI := isIso_homologyMap_succ_of_cycle_lifts f n hlift hdetect
  exact asIso (HomologicalComplex.homologyMap f (n + 1))

/-- The comparison keeps the original cohomology map as its forward morphism. -/
@[simp]
theorem homologyIsoOfCycleLifts_hom (f : K ⟶ L) (n : ℕ)
    (hlift : ∀ (z : L.X (n + 1)), L.d (n + 1) (n + 2) z = 0 →
      ∃ x : K.X (n + 1), K.d (n + 1) (n + 2) x = 0 ∧ f.f (n + 1) x = z)
    (hdetect : ∀ (x : K.X (n + 1)), K.d (n + 1) (n + 2) x = 0 →
      (∃ b : L.X n, L.d n (n + 1) b = f.f (n + 1) x) →
        ∃ a : K.X n, K.d n (n + 1) a = x) :
    (homologyIsoOfCycleLifts f n hlift hdetect).hom =
      HomologicalComplex.homologyMap f (n + 1) := rfl

end CochainComplex

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.GlobalQuasiIsoCriteria
