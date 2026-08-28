import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureShortLog
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureExponential

/-!
# Short segments in the quaternionic complex-structure space

Every pair in the common short-logarithm domain has an actual exponential
segment in the complex-structure locus. The segments vary continuously with
both endpoints, hit those endpoints, and are constant on diagonal pairs.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open Exponential

variable {n : ℕ}

private theorem real_smul_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (t : ℝ) :
    t • (0 : V) = 0 := smul_zero t

theorem continuous_of_toSymplectic {X : Type*} [TopologicalSpace X]
    {f : X → Space n} (h : Continuous (fun x ↦ toSymplectic (f x))) : Continuous f := by
  have h₁ : Continuous (fun x ↦ (toSymplectic (f x)).val) := continuous_subtype_val.comp h
  have h₂ : Continuous (fun x ↦ (toSymplectic (f x)).val.val) := continuous_subtype_val.comp h₁
  have hop : Continuous (fun x ↦ (toSymplectic (f x)).val.val.val) :=
    continuous_subtype_val.comp h₂
  exact (hop.subtype_mk _).subtype_mk _

namespace ShortLog

def direction (J J' : Space n) (h : (J, J') ∈ domain n) : AntiSkewSpace J :=
  ⟨(generator J J').val, ⟨(generator J J').property, generator_anticommute h⟩⟩

theorem direction_toSkew (J J' : Space n) (h : (J, J') ∈ domain n) :
    antiSkewToSkew J (direction J J' h) = generator J J' := rfl

def segment (J J' : Space n) (h : (J, J') ∈ domain n) (t : ℝ) : Space n :=
  exponentialCurve J (direction J J' h) t

theorem segment_toSymplectic (J J' : Space n) (h : (J, J') ∈ domain n) (t : ℝ) :
    toSymplectic (segment J J' h t) = toSymplectic J * exp (t • generator J J') :=
  exponentialCurve_toSymplectic J (direction J J' h) t

theorem segment_zero (J J' : Space n) (h : (J, J') ∈ domain n) :
    segment J J' h 0 = J := exponentialCurve_zero J (direction J J' h)

theorem segment_one (J J' : Space n) (h : (J, J') ∈ domain n) :
    segment J J' h 1 = J' := by
  apply toSymplectic_injective
  rw [segment_toSymplectic, one_smul, exp_generator h, Cayley.relative, mul_inv_cancel_left]

theorem segment_self (J : Space n) (t : ℝ) :
    segment J J (diagonal_mem_domain J) t = J := by
  apply toSymplectic_injective
  rw [segment_toSymplectic, generator_self]
  have hz : t • (0 : SkewSpace n) = 0 := real_smul_zero (V := SkewSpace n) t
  rw [hz, exp_zero, mul_one]

theorem continuous_segment :
    Continuous (fun p : domain n × ℝ ↦ segment p.1.val.1 p.1.val.2 p.1.property p.2) := by
  apply continuous_of_toSymplectic
  have hleft : Continuous (fun p : domain n × ℝ ↦ toSymplectic p.1.val.1) :=
    continuous_toSymplectic.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  have hgen : Continuous (fun p : domain n × ℝ ↦ generator p.1.val.1 p.1.val.2) :=
    continuous_generator.comp continuous_fst
  have he : Continuous (fun p : domain n × ℝ ↦ exp (p.2 • generator p.1.val.1 p.1.val.2)) :=
    contMDiff_exp.continuous.comp (continuous_snd.smul hgen)
  exact (hleft.mul he).congr (fun p ↦ (segment_toSymplectic _ _ _ _).symm)

def family : C(domain n × ℝ, Space n) :=
  ⟨fun p ↦ segment p.1.val.1 p.1.val.2 p.1.property p.2, continuous_segment⟩

def path (J J' : Space n) (h : (J, J') ∈ domain n) : Path J J' where
  toFun t := segment J J' h t
  continuous_toFun := (continuous_exponentialCurve J (direction J J' h)).comp
    continuous_subtype_val
  source' := segment_zero J J' h
  target' := segment_one J J' h

theorem segment_reverse (J J' : Space n) (h : (J, J') ∈ domain n) (t : ℝ) :
    segment J' J (swap_mem_domain h) t = segment J J' h (1 - t) := by
  apply toSymplectic_injective
  rw [segment_toSymplectic, segment_toSymplectic, generator_swap h]
  have hend : toSymplectic J' = toSymplectic J * exp (generator J J') := by
    rw [exp_generator h, Cayley.relative, mul_inv_cancel_left]
  rw [hend, mul_assoc]
  have hneg : t • -(generator J J') = (-t) • generator J J' := by
    exact (smul_neg t (generator J J')).trans (neg_smul t (generator J J')).symm
  rw [hneg]
  have hone : exp (generator J J') = exp ((1 : ℝ) • generator J J') := by rw [one_smul]
  rw [hone, ← exp_add_smul]
  exact congrArg (fun s : ℝ ↦ toSymplectic J * exp (s • generator J J')) (by ring)

end ShortLog
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
