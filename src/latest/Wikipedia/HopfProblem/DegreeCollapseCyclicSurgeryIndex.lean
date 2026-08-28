import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A strict finite-order decrease from an integral surgery relation

For an infinite-order meridian mu, the relation l*epsilon+n*mu=0
compares the indices of their cyclic subgroups. A common subgroup generated
by l*epsilon=-n*mu gives the exact cross-multiplied cardinality formula.
No splitting of the ambient abelian group or torsion-free hypothesis on
that group is needed.
-/

noncomputable section

open Function AddSubgroup

namespace Wikipedia.HopfProblem.DegreeCollapse.CyclicSurgeryIndex

variable {G : Type*} [AddCommGroup G]

theorem multiple_index (x : G) (hx : Injective (fun k : ℤ ↦ k • x)) (n : ℤ) :
    (zmultiples (n • x)).index = n.natAbs * (zmultiples x).index := by
  have hr := relIndex_map_map_of_injective (zmultiples n) (⊤ : AddSubgroup ℤ)
    (f := zmultiplesHom G x) hx
  have htop : (⊤ : AddSubgroup ℤ).map (zmultiplesHom G x) = zmultiples x := by
    ext y
    constructor
    · rintro ⟨k, _, rfl⟩
      exact zsmul_mem_zmultiples x k
    · rintro ⟨k, rfl⟩
      exact ⟨k, trivial, rfl⟩
  rw [AddMonoidHom.map_zmultiples, htop,
    relIndex_top_right, Int.index_zmultiples] at hr
  have hle : zmultiples (n • x) ≤ zmultiples x :=
    zmultiples_le.mpr (zsmul_mem_zmultiples x n)
  exact (relIndex_mul_index hle).symm.trans (congrArg (· * (zmultiples x).index) hr)

theorem coefficient_injective (ε μ : G) (hμ : Injective (fun k : ℤ ↦ k • μ))
    (l n : ℤ) (hn : n ≠ 0) (h : l • ε + n • μ = 0) :
    Injective (fun k : ℤ ↦ k • ε) := by
  have he : n • μ = -(l • ε) := eq_neg_of_add_eq_zero_left ((add_comm (n • μ) (l • ε)).trans h)
  intro a b hab
  have hm : (a * n) • μ = (b * n) • μ := by
    calc
      (a * n) • μ = -(l • (a • ε)) := by
        rw [mul_zsmul, he, smul_neg, ← mul_zsmul, mul_comm a l, mul_zsmul]
      _ = -(l • (b • ε)) := congrArg (fun z ↦ -(l • z)) hab
      _ = (b * n) • μ := by
        symm
        rw [mul_zsmul, he, smul_neg, ← mul_zsmul, mul_comm b l, mul_zsmul]
  exact mul_right_cancel₀ hn (hμ hm)

theorem relation_index (ε μ : G) (hμ : Injective (fun k : ℤ ↦ k • μ))
    (l n : ℤ) (hn : n ≠ 0) (h : l • ε + n • μ = 0) :
    l.natAbs * (zmultiples ε).index = n.natAbs * (zmultiples μ).index := by
  have he : l • ε = -(n • μ) := eq_neg_of_add_eq_zero_left h
  calc
    _ = (zmultiples (l • ε)).index := (multiple_index ε (coefficient_injective ε μ hμ l n hn h) l).symm
    _ = (zmultiples (n • μ)).index := by rw [he, zmultiples_neg]
    _ = _ := multiple_index μ hμ n

theorem strict_index_decrease (ε μ : G) (hμ : Injective (fun k : ℤ ↦ k • μ))
    (l n : ℤ) (hn : n ≠ 0) (hsmall : n.natAbs < l.natAbs)
    (h : l • ε + n • μ = 0) (hfinite : (zmultiples μ).index ≠ 0) :
    (zmultiples ε).index ≠ 0 ∧ (zmultiples ε).index < (zmultiples μ).index := by
  have hi := relation_index ε μ hμ l n hn h
  have hnpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hmupos : 0 < (zmultiples μ).index := Nat.pos_of_ne_zero hfinite
  have hepos : (zmultiples ε).index ≠ 0 := by
    intro he
    rw [he, mul_zero] at hi
    exact (Nat.mul_pos hnpos hmupos).ne' hi.symm
  refine ⟨hepos, ?_⟩
  have hmul : l.natAbs * (zmultiples ε).index < l.natAbs * (zmultiples μ).index := by
    rw [hi]
    exact Nat.mul_lt_mul_of_pos_right hsmall hmupos
  exact (Nat.mul_lt_mul_left (hnpos.trans hsmall)).mp hmul

theorem span_toAddSubgroup [Module ℤ G] (x : G) :
    (Submodule.span ℤ {x}).toAddSubgroup = zmultiples x := by
  ext y
  change y ∈ Submodule.span ℤ {x} ↔ y ∈ zmultiples x
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hy
    exact mem_zmultiples_iff.mpr
      ⟨k, (int_smul_eq_zsmul (inferInstance : Module ℤ G) k x).symm.trans hk⟩
  · intro hy
    obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp hy
    exact Submodule.mem_span_singleton.mpr
      ⟨k, (int_smul_eq_zsmul (inferInstance : Module ℤ G) k x).trans hk⟩

theorem quotient_span_card [Module ℤ G] (x : G) :
    Nat.card (G ⧸ Submodule.span ℤ {x}) = (zmultiples x).index := by
  change Nat.card (G ⧸ (Submodule.span ℤ {x}).toAddSubgroup) = _
  rw [span_toAddSubgroup]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.CyclicSurgeryIndex
