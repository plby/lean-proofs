import Wikipedia.HopfProblem.SheafLerayCurveVanishing
import Wikipedia.HopfProblem.SheafLerayCurveCyclesSequenceVanishing
import Wikipedia.HopfProblem.SheafLerayLowDegreesTransport

/-!
# The genuine curve-type short exact sequence of a complex

The proved finite homology-object vanishings identify degree-one Ext
of cycles with degree-one Ext of homology and annihilate the actual
degree-two cycle obstruction. The original cycles sequence therefore
becomes short exact, with no spectral-sequence or exactness premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve.Abstract

open SheafLerayLowDegrees.Abstract (homComplex)

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) (K : CochainComplex C ℕ) (hI : ∀ q : ℕ, Injective (K.X q))
  (n : ℕ) (h : HigherVanishing A K (n + 3))

/-- The left edge is the inverse of the actual quotient-induced Ext
comparison followed by the original cycles injection. -/
def curveFirstMap : AddCommGrpCat.of (Ext A (K.homology (n + 1)) 1) ⟶
    (homComplex A K).homology (n + 2) := by
  letI : Injective (K.X (n + 1)) := hI (n + 1)
  exact (cyclesHomologyExtOneIso A K hI (n + 3) h n le_rfl).inv ≫
    cyclesFirstMap A K (n + 1)

/-- The right edge remains the original cycle-quotient map, which is
defined even before imposing any vanishing hypotheses. -/
abbrev curveEdgeMap : (homComplex A K).homology (n + 2) ⟶
    AddCommGrpCat.of (A ⟶ K.homology (n + 2)) :=
  cyclesEdgeMap A K (n + 1)

theorem curveFirstMap_edgeMap : curveFirstMap A K hI n h ≫ curveEdgeMap A K n = 0 := by
  let : Injective (K.X (n + 1)) := hI (n + 1)
  change ((cyclesHomologyExtOneIso A K hI (n + 3) h n le_rfl).inv ≫
    cyclesFirstMap A K (n + 1)) ≫ cyclesEdgeMap A K (n + 1) = 0
  rw [Category.assoc, cyclesFirstMap_edgeMap, Limits.comp_zero]

/-- All three groups are the native Ext and original Hom-complex homology groups. -/
def curveComplex : ShortComplex AddCommGrpCat.{0} :=
  ShortComplex.mk (curveFirstMap A K hI n h) (curveEdgeMap A K n)
    (curveFirstMap_edgeMap A K hI n h)

/-- The original cycles sequence is identified by the actual quotient-induced
left comparison, while its middle and right groups and maps are retained. -/
def cyclesCurveComplexIso :
    letI := hI (n + 1)
    cyclesFirstComplex A K (n + 1) ≅ curveComplex A K hI n h := by
  letI := hI (n + 1)
  refine ShortComplex.isoMk
    (cyclesHomologyExtOneIso A K hI (n + 3) h n le_rfl)
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · change (cyclesHomologyExtOneIso A K hI (n + 3) h n le_rfl).hom ≫
      ((cyclesHomologyExtOneIso A K hI (n + 3) h n le_rfl).inv ≫
        cyclesFirstMap A K (n + 1)) = cyclesFirstMap A K (n + 1) ≫ 𝟙 _
    simp only [Iso.hom_inv_id_assoc, Category.comp_id]
  · change (𝟙 _) ≫ cyclesEdgeMap A K (n + 1) = cyclesEdgeMap A K (n + 1) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- Genuine short exactness follows from the proved cycle Ext vanishing
and the original exact cycles sequence. -/
theorem curveComplex_shortExact : (curveComplex A K hI n h).ShortExact := by
  let : Injective (K.X (n + 1)) := hI (n + 1)
  let : Subsingleton (Ext A (K.cycles (n + 1)) 2) :=
    cycles_ext_subsingleton A K hI (n + 3) h (n + 1) 2 (by omega) (by omega)
  exact ShortComplex.shortExact_of_iso (cyclesCurveComplexIso A K hI n h)
    (cyclesFirstComplex_shortExact A K (n + 1))

/-- The native map formulation of the actual short exact sequence. -/
theorem curve_exact :
    Function.Injective (curveFirstMap A K hI n h) ∧
      Function.Exact (curveFirstMap A K hI n h) (curveEdgeMap A K n) ∧
        Function.Surjective (curveEdgeMap A K n) := by
  have hs := curveComplex_shortExact A K hI n h
  exact ⟨(AddCommGrpCat.mono_iff_injective _).mp hs.mono_f,
    (ShortComplex.ab_exact_iff_function_exact _).mp hs.exact,
    (AddCommGrpCat.epi_iff_surjective _).mp hs.epi_g⟩

end Wikipedia.HopfProblem.SheafLerayCurve.Abstract
