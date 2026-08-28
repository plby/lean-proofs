import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorProjection
import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorInterval

/-! # The actual circle fiber of the rank-six spinor map -/

noncomputable section

namespace NoExoticSixSphere.RankSixComplexProjection.SpinorFibration

def map : C(UnitSpinor, OrthogonalComplexStructures.Space 6) :=
  ⟨fromSpinor, continuous_fromSpinor⟩

def coordinate (a b : UnitSpinor) (h : fromSpinor a = fromSpinor b) : Circle :=
  unitPhase (fromSpinor a) b a
    (by rw [h]; exact projection_fromSpinor_fixed b) (projection_fromSpinor_fixed a)

theorem coordinate_coe (a b : UnitSpinor) (h : fromSpinor a = fromSpinor b) :
    (coordinate a b h : ℂ) = inner ℂ (a : Spinor) (b : Spinor) := rfl

theorem phaseSmul_coordinate (a b : UnitSpinor) (h : fromSpinor a = fromSpinor b) :
    phaseSmul (coordinate a b h) a = b := unitPhase_smul _ _ _ _ _

theorem coordinate_self (a : UnitSpinor) (h : fromSpinor a = fromSpinor a) :
    coordinate a a h = 1 := by
  apply Subtype.ext
  change inner ℂ (a : Spinor) (a : Spinor) = 1
  rw [inner_self_eq_norm_sq_to_K, unitSpinor_norm]
  simp

theorem coordinate_phaseSmul (a : UnitSpinor) (z : Circle)
    (h : fromSpinor a = fromSpinor (phaseSmul z a)) : coordinate a (phaseSmul z a) h = z := by
  apply Subtype.ext
  change inner ℂ (a : Spinor) ((z : ℂ) • (a : Spinor)) = (z : ℂ)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, unitSpinor_norm]
  simp

theorem coordinate_mul (a b c : UnitSpinor) (hab : fromSpinor a = fromSpinor b)
    (hbc : fromSpinor b = fromSpinor c) (hac : fromSpinor a = fromSpinor c) :
    coordinate a b hab * coordinate b c hbc = coordinate a c hac := by
  apply Subtype.ext
  have he := congrArg (fun q : UnitSpinor ↦ inner ℂ (a : Spinor) (q : Spinor))
    (phaseSmul_coordinate b c hbc)
  change inner ℂ (a : Spinor) ((coordinate b c hbc : ℂ) • (b : Spinor)) =
    inner ℂ (a : Spinor) (c : Spinor) at he
  rw [inner_smul_right] at he
  exact (mul_comm _ _).trans he

theorem continuous_coordinate_family {X : Type*} [TopologicalSpace X]
    (a b : X → UnitSpinor) (ha : Continuous a) (hb : Continuous b)
    (h : ∀ x, fromSpinor (a x) = fromSpinor (b x)) :
    Continuous (fun x ↦ coordinate (a x) (b x) (h x)) :=
  ((continuous_subtype_val.comp ha).inner (continuous_subtype_val.comp hb)).subtype_mk _

theorem phaseSmul_mul (z w : Circle) (q : UnitSpinor) :
    phaseSmul (z * w) q = phaseSmul z (phaseSmul w q) :=
  Subtype.ext (mul_smul (z : ℂ) (w : ℂ) (q : Spinor))

abbrev fiber (a : UnitSpinor) := {b : UnitSpinor // fromSpinor b = fromSpinor a}

def fiberHomeomorph (a : UnitSpinor) : Circle ≃ₜ fiber a where
  toFun z := ⟨phaseSmul z a, fromSpinor_phaseSmul z a⟩
  invFun b := coordinate a b.val b.property.symm
  left_inv z := coordinate_phaseSmul a z _
  right_inv b := Subtype.ext (phaseSmul_coordinate a b.val b.property.symm)
  continuous_toFun :=
    (continuous_phaseSmul.comp (continuous_id.prodMk continuous_const)).subtype_mk _
  continuous_invFun := continuous_coordinate_family (fun _ ↦ a) Subtype.val
    continuous_const continuous_subtype_val _

theorem fiberHomeomorph_one (a : UnitSpinor) : fiberHomeomorph a 1 = ⟨a, rfl⟩ :=
  Subtype.ext (phaseSmul_one a)

end NoExoticSixSphere.RankSixComplexProjection.SpinorFibration
