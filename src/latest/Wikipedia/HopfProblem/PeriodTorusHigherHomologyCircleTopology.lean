import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.NormNum
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyIntervals

/-!
# An explicit two-arc cover of the actual additive circle

The circle is the actual quotient `AddCircle (1 : ℝ)`. The two open arcs
are the complements of zero and one half. Mathlib's local quotient chart
identifies each with an actual open real interval. Their intersection
has the two interval components required in the circle Mayer--Vietoris
calculation.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology

abbrev Circle := AddCircle (1 : ℝ)

/-- The point opposite the chosen circle origin. -/
def halfPoint : Circle := ((1 / 2 : ℝ) : Circle)

theorem halfPoint_ne_zero : halfPoint ≠ 0 := by
  intro h
  have he := (AddCircle.coe_eq_zero_iff_of_mem_Ico
    (p := (1 : ℝ)) (a := (1 / 2 : ℝ)) (by norm_num)).mp h
  norm_num at he

/-- The first actual open arc omits the origin. -/
def arcU : Set Circle := ({0} : Set Circle)ᶜ

/-- The second actual open arc omits the opposite point. -/
def arcV : Set Circle := ({halfPoint} : Set Circle)ᶜ

@[simp] theorem mem_arcU (x : Circle) : x ∈ arcU ↔ x ≠ 0 := Iff.rfl

@[simp] theorem mem_arcV (x : Circle) : x ∈ arcV ↔ x ≠ halfPoint := Iff.rfl

theorem arcU_open : IsOpen arcU := isOpen_compl_singleton

theorem arcV_open : IsOpen arcV := isOpen_compl_singleton

/-- The two explicitly punctured arcs cover the actual circle. -/
theorem arc_cover : arcU ∪ arcV = univ := by
  ext x
  simp only [mem_union, mem_arcU, mem_arcV, mem_univ, iff_true]
  by_cases hx : x = 0
  · right
    rw [hx]
    exact Ne.symm halfPoint_ne_zero
  · exact Or.inl hx

/-- A full open period interval is homeomorphic to the circle with its
identified endpoint removed; the inverse is the genuine quotient map. -/
def puncturedCircleHomeomorph (a : ℝ) :
    ({(a : Circle)}ᶜ : Set Circle) ≃ₜ Ioo a (a + 1) :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).toHomeomorphSourceTarget.symm

@[simp] theorem puncturedCircleHomeomorph_symm_coe (a : ℝ) (t : Ioo a (a + 1)) :
    ((puncturedCircleHomeomorph a).symm t : Circle) = ((t : ℝ) : Circle) := rfl

/-- The real interval coordinate projects back to the original circle point. -/
@[simp] theorem puncturedCircleHomeomorph_coe (a : ℝ)
    (x : ({(a : Circle)}ᶜ : Set Circle)) :
    (((puncturedCircleHomeomorph a x : Ioo a (a + 1)) : ℝ) : Circle) = (x : Circle) :=
  congrArg Subtype.val ((puncturedCircleHomeomorph a).symm_apply_apply x)

/-- The first arc has the actual coordinate interval `(0,1)`. -/
def arcUHomeomorph : arcU ≃ₜ Ioo (0 : ℝ) 1 :=
  (puncturedCircleHomeomorph 0).trans (Homeomorph.setCongr (by simp))

/-- The second arc has the actual coordinate interval `(1/2,3/2)`. -/
def arcVHomeomorph : arcV ≃ₜ Ioo (1 / 2 : ℝ) (3 / 2) :=
  (puncturedCircleHomeomorph (1 / 2)).trans (Homeomorph.setCongr (by norm_num))

@[simp] theorem arcUHomeomorph_symm_coe (t : Ioo (0 : ℝ) 1) :
    (arcUHomeomorph.symm t : Circle) = ((t : ℝ) : Circle) := rfl

@[simp] theorem arcVHomeomorph_symm_coe (t : Ioo (1 / 2 : ℝ) (3 / 2)) :
    (arcVHomeomorph.symm t : Circle) = ((t : ℝ) : Circle) := rfl

@[simp] theorem arcUHomeomorph_coe (x : arcU) :
    (((arcUHomeomorph x : Ioo (0 : ℝ) 1) : ℝ) : Circle) = (x : Circle) :=
  congrArg Subtype.val (arcUHomeomorph.symm_apply_apply x)

@[simp] theorem arcVHomeomorph_coe (x : arcV) :
    (((arcVHomeomorph x : Ioo (1 / 2 : ℝ) (3 / 2)) : ℝ) : Circle) = (x : Circle) :=
  congrArg Subtype.val (arcVHomeomorph.symm_apply_apply x)

theorem arcU_nonempty : arcU.Nonempty := ⟨halfPoint, halfPoint_ne_zero⟩

theorem arcV_nonempty : arcV.Nonempty := ⟨0, Ne.symm halfPoint_ne_zero⟩

instance arcUContractible : ContractibleSpace arcU := by
  let : ContractibleSpace (Ioo (0 : ℝ) 1) := intervalContractible 0 1 zero_lt_one
  exact arcUHomeomorph.contractibleSpace

instance arcVContractible : ContractibleSpace arcV := by
  let : ContractibleSpace (Ioo (1 / 2 : ℝ) (3 / 2)) :=
    intervalContractible (1 / 2) (3 / 2) (by norm_num)
  exact arcVHomeomorph.contractibleSpace

instance leftIntervalContractible : ContractibleSpace (Ioo (0 : ℝ) (1 / 2)) :=
  intervalContractible 0 (1 / 2) (by norm_num)

instance rightIntervalContractible : ContractibleSpace (Ioo (1 / 2 : ℝ) 1) :=
  intervalContractible (1 / 2) 1 (by norm_num)

/-- Intersecting two actual subsets is the same topological subtype as
first restricting to one and then imposing the other membership condition. -/
def intersectionSubtypeHomeomorph {T : Type*} [TopologicalSpace T] (U V : Set T) :
    ↥(U ∩ V) ≃ₜ {x : U // (x : T) ∈ V} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- In the first arc chart, omitting the opposite circle point means
omitting the actual real midpoint. -/
theorem arcU_mem_arcV_iff (x : arcU) :
    (x : Circle) ∈ arcV ↔ (arcUHomeomorph x : ℝ) ≠ 1 / 2 := by
  change (x : Circle) ≠ halfPoint ↔ _
  let m : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  have hm : (arcUHomeomorph.symm m : Circle) = halfPoint := rfl
  constructor
  · intro hx ht
    have ht' : arcUHomeomorph x = m := Subtype.ext ht
    have hx' : x = arcUHomeomorph.symm m :=
      (arcUHomeomorph.symm_apply_apply x).symm.trans (congrArg arcUHomeomorph.symm ht')
    exact hx ((congrArg Subtype.val hx').trans hm)
  · intro hx ht
    have hx' : x = arcUHomeomorph.symm m := Subtype.ext (ht.trans hm.symm)
    apply hx
    change (arcUHomeomorph x : ℝ) = (m : ℝ)
    rw [hx', Homeomorph.apply_symm_apply]

/-- The actual intersection chart is the punctured open unit interval. -/
def intersectionPuncturedHomeomorph :
    ↥(arcU ∩ arcV) ≃ₜ {t : Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2} :=
  (intersectionSubtypeHomeomorph arcU arcV).trans
    (arcUHomeomorph.subtype arcU_mem_arcV_iff)

/-- The actual intersection is the disjoint topological union of its
two explicit, contractible open interval components. -/
def intersectionHomeomorph :
    ↥(arcU ∩ arcV) ≃ₜ (Ioo (0 : ℝ) (1 / 2) ⊕ Ioo (1 / 2 : ℝ) 1) :=
  intersectionPuncturedHomeomorph.trans puncturedIntervalHomeomorph

@[simp] theorem intersectionHomeomorph_symm_inl_coe (t : Ioo (0 : ℝ) (1 / 2)) :
    (intersectionHomeomorph.symm (Sum.inl t) : Circle) = ((t : ℝ) : Circle) := rfl

@[simp] theorem intersectionHomeomorph_symm_inr_coe (t : Ioo (1 / 2 : ℝ) 1) :
    (intersectionHomeomorph.symm (Sum.inr t) : Circle) = ((t : ℝ) : Circle) := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology
