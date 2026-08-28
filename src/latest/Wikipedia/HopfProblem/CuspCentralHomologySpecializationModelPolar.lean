import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelBasic
import Wikipedia.HopfProblem.CuspCollapseFibreTorus

/-!
# Polar coordinates on an actual positive-real toric fibre

On a positive-real nonzero time fibre the third compact polar phase is
one.  The remaining two phases and the literal positive fibre therefore
give a bijective proper map onto the original toric fibre.  The resulting
homeomorphism uses the existing subspace topologies, and its positive
inverse coordinate is exactly the original modulus map.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace

theorem positiveFibre_isClosed (ρ : ℝ) :
    IsClosed {q : PositivePart | time (q : Space) = (ρ : ℂ)} :=
  isClosed_eq (time_holomorphic.continuous.comp continuous_subtype_val) continuous_const

theorem positiveFibreVal_isClosedEmbedding (ρ : ℝ) :
    IsClosedEmbedding (fun q : PositiveFibre ρ => (q.1 : Space)) :=
  positivePart_isClosed.isClosedEmbedding_subtypeVal.comp
    (positiveFibre_isClosed ρ).isClosedEmbedding_subtypeVal

/-- The original fibre-phase action, with its codomain restricted to fixed time. -/
def positiveFibrePolarMap (ρ : ℝ)
    (p : CompactFibreTorus × PositiveFibre ρ) : ToricFibre (ρ : ℂ) :=
  ⟨compactFibreAction p.1 (p.2.1 : Space), by
    rw [time_compactFibreAction, p.2.2]⟩

@[simp] theorem positiveFibrePolarMap_coe (ρ : ℝ)
    (p : CompactFibreTorus × PositiveFibre ρ) :
    (positiveFibrePolarMap ρ p : Space) = compactFibreAction p.1 (p.2.1 : Space) := rfl

theorem positiveFibrePolarMap_continuous (ρ : ℝ) : Continuous (positiveFibrePolarMap ρ) :=
  (compactFibreAction_continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_subtype_val).comp
      continuous_snd))).subtype_mk _

@[simp] theorem modulus_positiveFibrePolarMap (ρ : ℝ)
    (p : CompactFibreTorus × PositiveFibre ρ) :
    modulus (positiveFibrePolarMap ρ p : Space) = (p.2.1 : Space) := by
  rw [positiveFibrePolarMap_coe, modulus_compactFibreAction]
  exact p.2.1.2

/-- The actual modulus, regarded in the positive fixed-height fibre. -/
def positiveFibreModulus (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ToricFibre (ρ : ℂ)) :
    PositiveFibre ρ :=
  ⟨modulusRetraction (x : Space), by
    rw [modulusRetraction_coe, time_modulus, x.2, Complex.norm_of_nonneg hρ]⟩

@[simp] theorem positiveFibreModulus_coe (ρ : ℝ) (hρ : 0 ≤ ρ)
    (x : ToricFibre (ρ : ℂ)) :
    ((positiveFibreModulus ρ hρ x).1 : Space) = modulus (x : Space) := rfl

theorem positiveFibreModulus_continuous (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Continuous (positiveFibreModulus ρ hρ) :=
  (modulusRetraction_continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem positiveFibreModulus_polarMap (ρ : ℝ) (hρ : 0 ≤ ρ)
    (p : CompactFibreTorus × PositiveFibre ρ) :
    positiveFibreModulus ρ hρ (positiveFibrePolarMap ρ p) = p.2 :=
  Subtype.ext (Subtype.ext (modulus_positiveFibrePolarMap ρ p))

theorem compactFibrePhase_injective : Function.Injective compactFibrePhase := by
  intro u v huv
  funext i
  fin_cases i
  · exact congrFun huv 0
  · exact congrFun huv 1

/-- The existing phase uniqueness away from time zero also applies to
the two-dimensional fibre subgroup. -/
theorem compactFibreAction_injective_of_time_ne_zero {x : Space} (hx : time x ≠ 0) :
    Function.Injective (fun u : CompactFibreTorus => compactFibreAction u x) := by
  intro u v huv
  apply compactFibrePhase_injective
  apply compactTorusAction_injective_of_time_ne_zero hx
  simpa only [← compactFibreAction_eq_compact] using huv

theorem positiveFibrePolarMap_injective (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Injective (positiveFibrePolarMap ρ) := by
  rintro ⟨u, x⟩ ⟨v, y⟩ h
  have hxy : x = y := by
    have hm := congrArg (positiveFibreModulus ρ hρ.le) h
    simpa only [positiveFibreModulus_polarMap] using hm
  subst y
  have hx : time (x.1 : Space) ≠ 0 := by
    rw [x.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'
  have huv : u = v := compactFibreAction_injective_of_time_ne_zero hx
    (congrArg Subtype.val h)
  exact Prod.ext huv rfl

/-- Positive real time forces the last full polar phase to be one. -/
theorem compactTorusPhase_two_eq_one_of_positive_time (ρ : ℝ) (hρ : 0 < ρ)
    {x : Space} (hx : time x = (ρ : ℂ)) (u : CompactTorus)
    (hu : compactTorusAction u (modulus x) = x) : u 2 = 1 := by
  have hm : time (modulus x) = (ρ : ℂ) := by
    rw [time_modulus, hx, Complex.norm_of_nonneg hρ.le]
  have ht := congrArg time hu
  rw [compactTorusAction, time_torusAction, compactTorusUnits_apply, hm, hx] at ht
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne')
  simpa only [Circle.coe_one, one_mul] using ht

/-- The literal modulus of a positive-time point needs only fibre phases. -/
theorem exists_compactFibreAction_modulus_of_positive_time (ρ : ℝ) (hρ : 0 < ρ)
    {x : Space} (hx : time x = (ρ : ℂ)) :
    ∃ u : CompactFibreTorus, compactFibreAction u (modulus x) = x := by
  obtain ⟨u, hu⟩ := exists_compactTorusAction_modulus x
  have hu2 := compactTorusPhase_two_eq_one_of_positive_time ρ hρ hx u hu
  let uf : CompactFibreTorus := ![u 0, u 1]
  have hf : compactFibrePhase uf = u := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hu2.symm
  refine ⟨uf, ?_⟩
  rw [compactFibreAction_eq_compact, hf]
  exact hu

theorem positiveFibrePolarMap_surjective (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Surjective (positiveFibrePolarMap ρ) := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactFibreAction_modulus_of_positive_time ρ hρ x.2
  exact ⟨(u, positiveFibreModulus ρ hρ.le x), Subtype.ext hu⟩

/-- Properness is inherited from the actual compact fibre action and the
closed positive-time subspace, without replacing either topology. -/
theorem positiveFibrePolarMap_isProperMap (ρ : ℝ) : IsProperMap (positiveFibrePolarMap ρ) := by
  have hinc : IsProperMap
      (fun p : CompactFibreTorus × PositiveFibre ρ => (p.1, (p.2.1 : Space))) :=
    ((Homeomorph.refl CompactFibreTorus).isClosedEmbedding.prodMap
      (positiveFibreVal_isClosedEmbedding ρ)).isProperMap
  have hcomp : IsProperMap ((Subtype.val : ToricFibre (ρ : ℂ) → Space) ∘
      positiveFibrePolarMap ρ) := compactFibreAction_isProperMap.comp hinc
  exact isProperMap_of_comp_of_inj (positiveFibrePolarMap_continuous ρ)
    continuous_subtype_val hcomp Subtype.val_injective

theorem positiveFibrePolarMap_isClosedMap (ρ : ℝ) : IsClosedMap (positiveFibrePolarMap ρ) :=
  (positiveFibrePolarMap_isProperMap ρ).isClosedMap

/-- The actual positive-real toric fibre is the product of compact fibre
phases and its literal positive fibre. -/
def positiveFibrePolarHomeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    (CompactFibreTorus × PositiveFibre ρ) ≃ₜ ToricFibre (ρ : ℂ) :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (positiveFibrePolarMap ρ)
      ⟨positiveFibrePolarMap_injective ρ hρ, positiveFibrePolarMap_surjective ρ hρ⟩)
    (positiveFibrePolarMap_continuous ρ) (positiveFibrePolarMap_isClosedMap ρ)

@[simp] theorem positiveFibrePolarHomeomorph_apply (ρ : ℝ) (hρ : 0 < ρ)
    (p : CompactFibreTorus × PositiveFibre ρ) :
    positiveFibrePolarHomeomorph ρ hρ p = positiveFibrePolarMap ρ p := rfl

@[simp] theorem positiveFibrePolarHomeomorph_coe (ρ : ℝ) (hρ : 0 < ρ)
    (p : CompactFibreTorus × PositiveFibre ρ) :
    (positiveFibrePolarHomeomorph ρ hρ p : Space) =
      compactFibreAction p.1 (p.2.1 : Space) := rfl

/-- The positive inverse coordinate is the literal modulus, not a chosen
representative in an auxiliary quotient. -/
@[simp] theorem positiveFibrePolarHomeomorph_symm_snd (ρ : ℝ) (hρ : 0 < ρ)
    (x : ToricFibre (ρ : ℂ)) :
    ((positiveFibrePolarHomeomorph ρ hρ).symm x).2 = positiveFibreModulus ρ hρ.le x := by
  have he : positiveFibrePolarMap ρ ((positiveFibrePolarHomeomorph ρ hρ).symm x) = x :=
    (positiveFibrePolarHomeomorph ρ hρ).apply_symm_apply x
  have hm := congrArg (positiveFibreModulus ρ hρ.le) he
  simpa only [positiveFibreModulus_polarMap] using hm

@[simp] theorem positiveFibrePolarHomeomorph_symm_positive_coe (ρ : ℝ) (hρ : 0 < ρ)
    (x : ToricFibre (ρ : ℂ)) :
    (((positiveFibrePolarHomeomorph ρ hρ).symm x).2.1 : Space) = modulus (x : Space) := by
  rw [positiveFibrePolarHomeomorph_symm_snd, positiveFibreModulus_coe]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
