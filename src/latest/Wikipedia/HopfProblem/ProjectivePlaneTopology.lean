import Wikipedia.HopfProblem.ProjectivePlaneCompact
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Ring

/-!
# Separation properties of the complex projective plane

The projection from nonzero homogeneous vectors is open.  Its equivalence
relation is the common zero locus of the two-by-two minors, so the quotient
topology is Hausdorff.  It is also second countable, and the imported unit
sphere argument supplies compactness.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ProjectivePlane

/-- Multiplication of a nonzero homogeneous vector by a complex unit. -/
def unitScale (a : ℂˣ) (v : NonzeroVector) : NonzeroVector :=
  ⟨a • (v : Homogeneous), by
    exact fun h => v.property ((MulAction.injective a) (by simpa using h))⟩

@[simp]
theorem unitScale_coe (a : ℂˣ) (v : NonzeroVector) :
    (unitScale a v : Homogeneous) = a • (v : Homogeneous) := rfl

theorem unitScale_continuous (a : ℂˣ) : Continuous (unitScale a) :=
  (continuous_const_smul a).comp continuous_subtype_val |>.subtype_mk _

@[simp]
theorem quotientMap_unitScale (a : ℂˣ) (v : NonzeroVector) :
    quotientMap (unitScale a v) = quotientMap v :=
  (quotientMap_eq_iff _ _).2 ⟨a, rfl⟩

/-- The canonical scalar-quotient projection is open. -/
theorem quotientMap_isOpenMap : IsOpenMap quotientMap := by
  intro U hU
  apply quotientMap_isQuotientMap.isOpen_preimage.mp
  have hs : quotientMap ⁻¹' (quotientMap '' U) =
      ⋃ a : ℂˣ, (unitScale a) ⁻¹' U := by
    ext v
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨w, hw, heq⟩
      obtain ⟨a, ha⟩ := (quotientMap_eq_iff w v).1 heq
      refine ⟨a, ?_⟩
      have he : unitScale a v = w := Subtype.ext ha
      simpa only [he] using hw
    · rintro ⟨a, ha⟩
      exact ⟨unitScale a v, ha, quotientMap_unitScale a v⟩
  rw [hs]
  exact isOpen_iUnion fun a => hU.preimage (unitScale_continuous a)

theorem quotientMap_isOpenQuotientMap : IsOpenQuotientMap quotientMap :=
  ⟨quotientMap_surjective, quotientMap_continuous, quotientMap_isOpenMap⟩

/-- Two nonzero homogeneous vectors define the same point precisely when
all their two-by-two minors vanish. -/
theorem quotientMap_eq_iff_minors (v w : NonzeroVector) :
    quotientMap v = quotientMap w ↔
      ∀ i j : Fin 3, (v : Homogeneous) i * (w : Homogeneous) j =
        (v : Homogeneous) j * (w : Homogeneous) i := by
  rw [quotientMap_eq_iff_scalar]
  constructor
  · rintro ⟨a, ha⟩ i j
    have hi : a * (w : Homogeneous) i = (v : Homogeneous) i := congrFun ha i
    have hj : a * (w : Homogeneous) j = (v : Homogeneous) j := congrFun ha j
    rw [← hi, ← hj]
    ring
  · intro h
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, (w : Homogeneous) j ≠ 0 := by
      by_contra! he
      exact w.property (funext he)
    refine ⟨(v : Homogeneous) j / (w : Homogeneous) j, ?_⟩
    funext i
    change ((v : Homogeneous) j / (w : Homogeneous) j) * (w : Homogeneous) i = _
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff hj).2 (h i j).symm

/-- The scalar-equivalence relation on nonzero vectors is closed. -/
theorem isClosed_quotientMap_relation :
    IsClosed {q : NonzeroVector × NonzeroVector | quotientMap q.1 = quotientMap q.2} := by
  have hs : {q : NonzeroVector × NonzeroVector | quotientMap q.1 = quotientMap q.2} =
      ⋂ i : Fin 3, ⋂ j : Fin 3,
        {q : NonzeroVector × NonzeroVector |
          (q.1 : Homogeneous) i * (q.2 : Homogeneous) j =
            (q.1 : Homogeneous) j * (q.2 : Homogeneous) i} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter, quotientMap_eq_iff_minors]
  rw [hs]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
  · exact ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))

instance spaceT2Space : T2Space Space :=
  (t2Space_iff_of_isOpenQuotientMap quotientMap_isOpenQuotientMap).2
    isClosed_quotientMap_relation

instance spaceSecondCountableTopology : SecondCountableTopology Space :=
  quotientMap_isQuotientMap.secondCountableTopology quotientMap_isOpenMap

end Wikipedia.HopfProblem.ProjectivePlane
