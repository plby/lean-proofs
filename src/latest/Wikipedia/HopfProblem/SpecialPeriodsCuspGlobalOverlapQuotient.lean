import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyQuotient
import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry

/-!
# Comparing the actual cyclic and triangle family quotients

The logarithmic family and the regular triangle family have the same real
coordinate torus.  An equivariant base inclusion therefore gives a literal
map between their actual orbit quotients.  This file proves its injectivity
from the precise-return criterion and identifies its entire image over the
base image.  The subsequent geometric specialization supplies that criterion
from the proved cusp stabilizer; no comparison map is assumed.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily

namespace QuotientComparison

variable (C : CuspFamily.Data)
    (D : TrianglePeriodFamily.Data ℂ TriangleRegularPoint)
    (f : LogBase C.radius → TriangleRegularPoint)

/-- The unchanged real torus coordinate over a supplied logarithmic base map. -/
def totalMap (x : C.TotalSpace) : D.TotalSpace := (f x.1, x.2)

@[simp] theorem totalMap_fst (x : C.TotalSpace) :
    (totalMap C D f x).1 = f x.1 := rfl

@[simp] theorem totalMap_snd (x : C.TotalSpace) :
    (totalMap C D f x).2 = x.2 := rfl

theorem totalMap_injective (hf : Injective f) : Injective (totalMap C D f) := by
  intro x y h
  exact Prod.ext (hf (congrArg Prod.fst h)) (congrArg (fun z : D.TotalSpace => z.2) h)

variable
    (hbase : ∀ (k : ℤ) (s : LogBase C.radius),
      f (logBaseTranslate C.radius k s) = triangleCuspGenerator ^ k • f s)
    (htorus : ∀ k : ℤ,
      triangleTorusHomeomorph (triangleCuspGenerator ^ k) = cuspTorusHomeomorph k)

include hbase htorus

/-- The actual clockwise integer action is the restriction of the actual
triangle action, including its integral action on every torus fibre. -/
theorem totalMap_equivariant (k : Multiplicative ℤ) (x : C.TotalSpace) :
    letI := C.totalAction
    letI := D.totalAction
    totalMap C D f (k • x) = triangleCuspGenerator ^ k.toAdd • totalMap C D f x := by
  let := C.totalAction
  let := D.totalAction
  change (f (logBaseTranslate C.radius k.toAdd x.1), cuspTorusHomeomorph k.toAdd x.2) =
    (triangleCuspGenerator ^ k.toAdd • f x.1,
      triangleTorusHomeomorph (triangleCuspGenerator ^ k.toAdd) x.2)
  rw [hbase, htorus]

/-- The genuine map between the two orbit quotients, obtained by descent
of the unchanged real torus coordinate. -/
def descend : C.Space → D.Space := by
  letI := C.totalAction
  letI := D.totalAction
  exact Quotient.lift (D.quotient ∘ totalMap C D f) (by
    rintro x y ⟨k, hk⟩
    change D.quotient (totalMap C D f x) = D.quotient (totalMap C D f y)
    rw [← hk, totalMap_equivariant C D f hbase htorus, D.quotient_smul])

@[simp] theorem descend_quotient (x : C.TotalSpace) :
    descend C D f hbase htorus (C.quotient x) = D.quotient (totalMap C D f x) := rfl

@[simp] theorem projection_descend_quotient (x : C.TotalSpace) :
    D.projection (descend C D f hbase htorus (C.quotient x)) =
      D.baseQuotient (f x.1) := rfl

/-- Precise cusp returns exclude every additional triangle identification.
Together with the injective logarithmic base inclusion this proves actual
injectivity after both quotient operations. -/
theorem descend_injective (hf : Injective f)
    (hreturn : ∀ (g : TriangleGroup) (s t : LogBase C.radius),
      g • f t = f s → ∃ k : ℤ, triangleCuspGenerator ^ k = g) :
    Injective (descend C D f hbase htorus) := by
  let := C.totalAction
  let := D.totalAction
  intro x y hxy
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  obtain ⟨b, rfl⟩ := C.quotient_surjective y
  obtain ⟨g, hg⟩ := (D.quotient_eq_iff _ _).mp hxy
  have hb : g • f b.1 = f a.1 := congrArg Prod.fst hg
  obtain ⟨k, rfl⟩ := hreturn g a.1 b.1 hb
  apply (C.quotient_eq_iff _ _).mpr
  refine ⟨Multiplicative.ofAdd k, ?_⟩
  apply totalMap_injective C D f hf
  rw [totalMap_equivariant C D f hbase htorus]
  exact hg

/-- The image consists of all fibres over the actual image of the logarithmic
base.  In particular the comparison does not merely identify chosen sections
or individual fibres. -/
theorem range_descend :
    range (descend C D f hbase htorus) =
      D.projection ⁻¹' range (D.baseQuotient ∘ f) := by
  let := D.totalAction
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := C.quotient_surjective x
    exact ⟨a.1, rfl⟩
  · rintro ⟨s, hs⟩
    obtain ⟨⟨b, t⟩, rfl⟩ := D.quotient_surjective y
    have hbase' : D.baseQuotient (f s) = D.baseQuotient b := hs
    have hrel : ∃ g : TriangleGroup, g • b = f s := Quotient.eq''.mp hbase'
    obtain ⟨g, hg⟩ := hrel
    refine ⟨C.quotient (s, triangleTorusHomeomorph g t), ?_⟩
    apply (D.quotient_eq_iff _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

end QuotientComparison

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
