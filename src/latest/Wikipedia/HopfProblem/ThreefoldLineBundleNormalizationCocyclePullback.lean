import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackHolomorphic
import Wikipedia.HopfProblem.HolomorphicPicardCechSheafMap
import Wikipedia.HopfProblem.HolomorphicExponentialSheafUnitsExponential

/-!
# Literal holomorphic Čech pullback on the original preimage cover

The cover is the actual `Opens.comap` of a holomorphic map. Local
sections are pulled back by the existing genuine holomorphic section
composition map. Both additive and unit cocycles retain their literal
values and their original triple-overlap identities. Ordinary complex
exponentiation commutes with this actual pullback.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.LineBundleNormalization.Cocycle

open HolomorphicFunctionSheaf.SphereH1 HolomorphicExponentialSheaf

variable {E H E' H' M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (f : ContMDiffMap J I N M ω)

/-- The literal inverse-image open of the original holomorphic map. -/
def preimageOpen (U : Opens M) : Opens N :=
  Opens.comap (⟨f, f.contMDiff.continuous⟩ : C(N, M)) U

@[simp] theorem mem_preimageOpen (U : Opens M) (x : N) :
    x ∈ preimageOpen f U ↔ f x ∈ U := Iff.rfl

/-- The literal original map on the actual inverse-image open. -/
def preimagePoint (U : Opens M) (x : preimageOpen f U) : U := ⟨f x, x.property⟩

/-- The previously constructed actual composition of holomorphic sections. -/
def sectionPullback (U : Opens M) :
    HolomorphicFunctionSheaf.Section I M U →+*
      HolomorphicFunctionSheaf.Section J N (preimageOpen f U) :=
  HolomorphicMeromorphic.holomorphicPullback J I f U

@[simp] theorem sectionPullback_apply (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M U) (x : preimageOpen f U) :
    sectionPullback f U s x = s (preimagePoint f U x) := rfl

/-- The preimage cover uses the same original index type. -/
def preimageCover {ι : Type} (U : ι → Opens M) : ι → Opens N :=
  fun i => preimageOpen f (U i)

/-- An actual covering family remains a covering family under preimage. -/
theorem preimageCover_covers {ι : Type} (U : ι → Opens M)
    (hU : ∀ x : M, ∃ i : ι, x ∈ U i) (x : N) :
    ∃ i : ι, x ∈ preimageCover f U i := hU (f x)

variable {ι : Type} {U : ι → Opens M}

/-- Pullback of the actual additive overlap sections on the literal
preimage cover, with its original triple-overlap identity. -/
def pullbackCocycle (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I M) U) :
    CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf J N) (preimageCover f U) where
  value i j := sectionPullback f (U i ⊓ U j) (c.value i j)
  condition i j k := by
    apply ContMDiffMap.ext
    intro x
    exact congrArg
      (fun s : HolomorphicFunctionSheaf.Section I M ((U i ⊓ U j) ⊓ U k) =>
        s ⟨f x, x.property⟩) (c.condition i j k)

/-- Every pulled-back additive value is literal composition with the
original map, with no cohomology comparison involved. -/
@[simp] theorem pullbackCocycle_value_apply
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I M) U)
    (i j : ι) (x : ↥(preimageCover f U i ⊓ preimageCover f U j)) :
    ((pullbackCocycle f c).value i j :
        HolomorphicFunctionSheaf.Section J N (preimageCover f U i ⊓ preimageCover f U j)) x =
      (c.value i j : HolomorphicFunctionSheaf.Section I M (U i ⊓ U j))
        ⟨f x, x.property⟩ := rfl

/-- Pullback of an original holomorphic unit uses the actual ring-unit
map of the actual section pullback. -/
def unitSectionPullback (V : Opens M) :
    UnitSection I M V →+ UnitSection J N (preimageOpen f V) :=
  (Units.map (sectionPullback f V).toMonoidHom).toAdditive

@[simp] theorem unitSectionPullback_eval (V : Opens M) (s : UnitSection I M V)
    (x : preimageOpen f V) :
    unitSectionEval (unitSectionPullback f V s) x =
      unitSectionEval s (preimagePoint f V x) := rfl

/-- The literal pullback of an original holomorphic unit cocycle. -/
def pullbackUnitsCocycle (c : CechOneCocycle (unitsSheaf I M) U) :
    CechOneCocycle (unitsSheaf J N) (preimageCover f U) where
  value i j := unitSectionPullback f (U i ⊓ U j) (c.value i j)
  condition i j k := by
    apply unitSection_ext
    intro x
    exact congrArg
      (fun s : UnitSection I M ((U i ⊓ U j) ⊓ U k) =>
        unitSectionEval s ⟨f x, x.property⟩) (c.condition i j k)

@[simp] theorem pullbackUnitsCocycle_value_eval
    (c : CechOneCocycle (unitsSheaf I M) U) (i j : ι)
    (x : ↥(preimageCover f U i ⊓ preimageCover f U j)) :
    unitSectionEval ((pullbackUnitsCocycle f c).value i j) x =
      unitSectionEval (c.value i j) ⟨f x, x.property⟩ := rfl

/-- The original ordinary exponential commutes with actual holomorphic
Čech pullback, as equality of the original unit cocycles. -/
theorem pullback_exponentialCocycle
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I M) U) :
    pullbackUnitsCocycle f (HolomorphicPicard.Cech.mapCocycle (exponential I M) c) =
      HolomorphicPicard.Cech.mapCocycle (exponential J N) (pullbackCocycle f c) := by
  apply HolomorphicPicard.Cech.cocycle_ext
  intro i j
  apply unitSection_ext
  intro x
  rfl

/-- The exponentiated pulled-back cocycle has exactly the pulled-back
native unit-transition values. -/
theorem pullback_exponentialCocycle_value_eval
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I M) U)
    (i j : ι) (x : ↥(preimageCover f U i ⊓ preimageCover f U j)) :
    unitSectionEval
        ((HolomorphicPicard.Cech.mapCocycle (exponential J N) (pullbackCocycle f c)).value i j) x =
      unitSectionEval ((HolomorphicPicard.Cech.mapCocycle (exponential I M) c).value i j)
        ⟨f x, x.property⟩ := rfl

end Wikipedia.HopfProblem.LineBundleNormalization.Cocycle
