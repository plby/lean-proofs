import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticAction
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusQuotient

/-!
# Explicit disc-product coordinates on a finite elliptic quotient

A genuine circle-valued fibre coordinate increasing by `1/m` under the
fibre generator cancels the clockwise disc rotation.  The resulting
homeomorphism is proved for the original orbit quotient and quotient
topology, with exact formulas in both directions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel

open SpecialPeriods ThreefoldOverlapMappingTorus
open Wikipedia.HopfProblem.Elliptic
open Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient

variable {X : Type*} [TopologicalSpace X]
variable (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)

/-- The actual product of the unchanged disc and the fibre-orbit projection. -/
def verticalProductMap : Disc × X → Disc × FibreQuotient m B hB :=
  Prod.map id (fibreProject m B hB)

theorem verticalProductMap_isOpenQuotientMap :
    IsOpenQuotientMap (verticalProductMap m B hB) :=
  IsOpenQuotientMap.id.prodMap (fibreProject_isOpenQuotientMap m B hB)

/-- The two actual quotient maps have precisely the same fibres. -/
theorem verticalProject_eq_iff (p q : Disc × X) :
    verticalProject m B hB p = verticalProject m B hB q ↔
      verticalProductMap m B hB p = verticalProductMap m B hB q := by
  let := fibreAction m B hB
  let := verticalAction m B hB
  change FiniteQuotient.project (Multiplicative (ZMod m)) (Disc × X) p =
    FiniteQuotient.project (Multiplicative (ZMod m)) (Disc × X) q ↔
      (p.1, fibreProject m B hB p.2) = (q.1, fibreProject m B hB q.2)
  rw [FiniteQuotient.project_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    have hp : (q.1, g • q.2) = p :=
      (verticalAction_smul m B hB g q).symm.trans hg
    apply Prod.ext
    · exact (congrArg Prod.fst hp).symm
    · change fibreProject m B hB p.2 = fibreProject m B hB q.2
      exact (FiniteQuotient.project_eq_iff_mem_orbit
        (Multiplicative (ZMod m)) X p.2 q.2).mpr ⟨g, congrArg Prod.snd hp⟩
  · intro h
    have hfirst : p.1 = q.1 :=
      congrArg (fun z : Disc × FibreQuotient m B hB => z.1) h
    have hsecond : fibreProject m B hB p.2 = fibreProject m B hB q.2 :=
      congrArg (fun z : Disc × FibreQuotient m B hB => z.2) h
    obtain ⟨g, hg⟩ := (FiniteQuotient.project_eq_iff_mem_orbit
      (Multiplicative (ZMod m)) X p.2 q.2).mp hsecond
    refine ⟨g, ?_⟩
    exact (verticalAction_smul m B hB g q).trans (Prod.ext hfirst.symm hg)

/-- Quotienting the vertical action leaves the disc as a genuine product factor. -/
def verticalProductHomeomorph :
    VerticalQuotient m B hB ≃ₜ Disc × FibreQuotient m B hB :=
  quotientHomeomorph (verticalProject m B hB) (verticalProductMap m B hB)
    (verticalProject_isOpenQuotientMap m B hB).isQuotientMap
    (verticalProductMap_isOpenQuotientMap m B hB).isQuotientMap
    (verticalProject_eq_iff m B hB)

@[simp] theorem verticalProductHomeomorph_project (p : Disc × X) :
    verticalProductHomeomorph m B hB (verticalProject m B hB p) =
      (p.1, fibreProject m B hB p.2) :=
  quotientHomeomorph_apply _ _ _ _ _ p

variable (χ : C(X, Circle)) (hχ : ∀ x, χ (B x) = χ x + sector m)

include hχ

omit [NeZero m] in
/-- The explicit fibre phase cancels the actual clockwise generator on the disc. -/
theorem untwist_capPermutation (p : Disc × X) :
    untwist χ (capPermutation m B p) = verticalPermutation B (untwist χ p) := by
  change (rotate (χ (B p.2)) (rotate (-sector m) p.1), B p.2) =
    (rotate (χ p.2) p.1, B p.2)
  rw [hχ, ← rotate_add, add_neg_cancel_right]

/-- The genuine quotient homeomorphism obtained from the generator conjugacy. -/
def capUntwistHomeomorph : CapQuotient m B hB ≃ₜ VerticalQuotient m B hB :=
  cyclicQuotientCongr (capPermutation m B) (capPermutation_pow_order m B hB)
    (verticalPermutation B) (verticalPermutation_pow_order m B hB)
    (untwist χ) (untwist_capPermutation m B χ hχ)

@[simp] theorem capUntwistHomeomorph_project (p : Disc × X) :
    capUntwistHomeomorph m B hB χ hχ (capProject m B hB p) =
      verticalProject m B hB (untwist χ p) :=
  cyclicQuotientCongr_project (capPermutation m B) (capPermutation_pow_order m B hB)
    (verticalPermutation B) (verticalPermutation_pow_order m B hB)
    (untwist χ) (untwist_capPermutation m B χ hχ) p

/-- A full disc-product homeomorphism, with the original fibre quotient as its second factor. -/
def capProductHomeomorph : CapQuotient m B hB ≃ₜ Disc × FibreQuotient m B hB :=
  (capUntwistHomeomorph m B hB χ hχ).trans (verticalProductHomeomorph m B hB)

/-- The forward formula is literal on every original quotient representative. -/
@[simp] theorem capProductHomeomorph_project (p : Disc × X) :
    capProductHomeomorph m B hB χ hχ (capProject m B hB p) =
      (rotate (χ p.2) p.1, fibreProject m B hB p.2) := by
  change verticalProductHomeomorph m B hB
    (capUntwistHomeomorph m B hB χ hχ (capProject m B hB p)) = _
  rw [capUntwistHomeomorph_project, verticalProductHomeomorph_project]
  rfl

/-- The inverse needs no argument branch; representatives differing by the finite action agree. -/
theorem capProductHomeomorph_symm_project (s : Disc) (x : X) :
    (capProductHomeomorph m B hB χ hχ).symm (s, fibreProject m B hB x) =
      capProject m B hB (rotate (-χ x) s, x) := by
  apply (capProductHomeomorph m B hB χ hχ).injective
  rw [Homeomorph.apply_symm_apply, capProductHomeomorph_project, rotate_rotate_neg]

/-- The product coordinate preserves the exact native root radius. -/
theorem capProductHomeomorph_project_norm (p : Disc × X) :
    ‖((capProductHomeomorph m B hB χ hχ (capProject m B hB p)).1 : ℂ)‖ =
      ‖(p.1 : ℂ)‖ := by
  rw [capProductHomeomorph_project, rotate_norm]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel
