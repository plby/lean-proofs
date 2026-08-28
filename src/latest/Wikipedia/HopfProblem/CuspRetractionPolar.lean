import Wikipedia.HopfProblem.ToricHausdorff
import Wikipedia.HopfProblem.CuspRetractionTorus
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.LocalAtTarget

/-!
# The genuine modulus retraction of the toric cusp space

Taking the modulus of every affine toric coordinate commutes with all the
integral monomial changes of coordinates, including the boundary strata.
Consequently these coordinate maps descend to a continuous idempotent map
of the actual glued space. Its image is the closure of the positive real
torus, with the subspace topology.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ProductRestriction

variable {K X Y : Type*} [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace Y]
    (f : K × X → Y) (B : Set X) (C : Set Y)
    (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B)

/-- An invariant restriction of a product map has the literal product
subspace topology. -/
def productPreimageHomeomorph : K × B ≃ₜ (f ⁻¹' C) where
  toFun p := ⟨(p.1, (p.2 : X)), (hpre _).mpr p.2.property⟩
  invFun p := (p.1.1, ⟨p.1.2, (hpre _).mp p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def productRestriction (p : K × B) : C :=
  ⟨f (p.1, (p.2 : X)), (hpre _).mpr p.2.property⟩

theorem productRestriction_continuous (hf : Continuous f) :
    Continuous (productRestriction f B C hpre) :=
  hf.restrictPreimage.comp (productPreimageHomeomorph f B C hpre).continuous

theorem productRestriction_isClosedMap (hf : IsClosedMap f) :
    IsClosedMap (productRestriction f B C hpre) :=
  (hf.restrictPreimage C).comp (productPreimageHomeomorph f B C hpre).isClosedMap

theorem productRestriction_isProperMap (hf : IsProperMap f) :
    IsProperMap (productRestriction f B C hpre) :=
  (hf.restrictPreimage C).comp (productPreimageHomeomorph f B C hpre).isProperMap

omit [TopologicalSpace Y] in
theorem productRestriction_surjective (hf : Function.Surjective f) :
    Function.Surjective (productRestriction f B C hpre) :=
  (hf.restrictPreimage C).comp (productPreimageHomeomorph f B C hpre).surjective

theorem productRestriction_isQuotientMap
    (hfcont : Continuous f) (hfclosed : IsClosedMap f) (hfsurj : Function.Surjective f) :
    IsQuotientMap (productRestriction f B C hpre) :=
  (productRestriction_isClosedMap f B C hpre hfclosed).isQuotientMap
    (productRestriction_continuous f B C hpre hfcont)
    (productRestriction_surjective f B C hpre hfsurj)

end Wikipedia.HopfProblem.ProductRestriction

namespace Wikipedia.HopfProblem.ToricCharts

variable {d : ℕ}

/-- Coordinatewise complex modulus, regarded again as a complex vector. -/
def coordinateModulus (z : CoordinateSpace d) : CoordinateSpace d :=
  fun i => (‖z i‖ : ℂ)

@[simp] theorem coordinateModulus_apply (z : CoordinateSpace d) (i : Fin d) :
    coordinateModulus z i = (‖z i‖ : ℂ) := rfl

theorem coordinateModulus_continuous :
    Continuous (coordinateModulus : CoordinateSpace d → CoordinateSpace d) := by
  exact continuous_pi fun i =>
    Complex.continuous_ofReal.comp (continuous_apply i).norm

@[simp] theorem coordinateModulus_idempotent (z : CoordinateSpace d) :
    coordinateModulus (coordinateModulus z) = coordinateModulus z := by
  funext i
  simp [coordinateModulus]

@[simp] theorem coordinateModulus_ne_zero_iff (z : CoordinateSpace d) (i : Fin d) :
    coordinateModulus z i ≠ 0 ↔ z i ≠ 0 := by
  simp [coordinateModulus]

@[simp] theorem coordinateModulus_mem_domain_iff
    (A : Matrix (Fin d) (Fin d) ℤ) (z : CoordinateSpace d) :
    coordinateModulus z ∈ domain A ↔ z ∈ domain A := by
  simp [domain]

@[simp] theorem coordinateModulus_mem_torus_iff (z : CoordinateSpace d) :
    coordinateModulus z ∈ torus ↔ z ∈ torus := by
  simp [torus]

/-- The norm identity is valid at zero as well as on the dense torus. -/
theorem monomial_coordinateModulus (A : Matrix (Fin d) (Fin d) ℤ)
    (z : CoordinateSpace d) :
    monomial A (coordinateModulus z) = coordinateModulus (monomial A z) := by
  funext i
  simp [monomial, coordinateModulus, norm_prod, norm_zpow]

/-- The ordinary nonnegative real orthant inside complex coordinate space. -/
def nonnegativeCoordinates : Set (CoordinateSpace d) :=
  {z | ∃ r : Fin d → ℝ, (∀ i, 0 ≤ r i) ∧ z = fun i => (r i : ℂ)}

/-- The strictly positive real orthant inside the dense coordinate torus. -/
def positiveCoordinates : Set (CoordinateSpace d) :=
  {z | ∃ r : Fin d → ℝ, (∀ i, 0 < r i) ∧ z = fun i => (r i : ℂ)}

theorem coordinateModulus_eq_self_iff (z : CoordinateSpace d) :
    coordinateModulus z = z ↔ z ∈ nonnegativeCoordinates := by
  constructor
  · intro hz
    exact ⟨fun i => ‖z i‖, fun i => norm_nonneg _, hz.symm⟩
  · rintro ⟨r, hr, rfl⟩
    funext i
    exact congrArg Complex.ofReal (Complex.norm_of_nonneg (hr i))

theorem positiveCoordinates_eq_modulus_image_torus :
    (positiveCoordinates : Set (CoordinateSpace d)) = coordinateModulus '' torus := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨fun i => (r i : ℂ), ?_, ?_⟩
    · intro i
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hr i))
    · funext i
      exact congrArg Complex.ofReal (Complex.norm_of_nonneg (hr i).le)
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun i => ‖w i‖, fun i => norm_pos_iff.mpr (hw i), rfl⟩

end Wikipedia.HopfProblem.ToricCharts

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

theorem chartChange_coordinateModulus (s t : Triangle) (z : CoordinateSpace 3) :
    chartChange s t (coordinateModulus z) = coordinateModulus (chartChange s t z) :=
  monomial_coordinateModulus (transition s t) z

theorem coordinateModulus_overlap (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    inclusion t (coordinateModulus (chartChange s t z)) =
      inclusion s (coordinateModulus z) := by
  symm
  apply (inclusion_eq_iff s t _ _).mpr
  refine ⟨?_, chartChange_coordinateModulus s t z⟩
  simpa only [chartChange_source, coordinateModulus_mem_domain_iff] using hz

/-- The global modulus on the actual toric gluing. -/
def modulus : Space → Space :=
  descend fun s z => inclusion s (coordinateModulus z)

@[simp] theorem modulus_inclusion (s : Triangle) (z : CoordinateSpace 3) :
    modulus (inclusion s z) = inclusion s (coordinateModulus z) :=
  descend_inclusion _ (fun s t _z hz => coordinateModulus_overlap s t hz) s z

theorem modulus_continuous : Continuous modulus := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  apply ((parametrization s).continuousAt_iff_continuousAt_comp_right
    (show inclusion s z ∈ (parametrization s).target by simp)).mpr
  have h : modulus ∘ parametrization s = inclusion s ∘ coordinateModulus := by
    funext w
    exact modulus_inclusion s w
  rw [h]
  exact ((inclusion_openEmbedding s).continuous.comp
    coordinateModulus_continuous).continuousAt

@[simp] theorem modulus_idempotent (x : Space) : modulus (modulus x) = modulus x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp only [modulus_inclusion, coordinateModulus_idempotent]

@[simp] theorem time_modulus (x : Space) : time (modulus x) = (‖time x‖ : ℂ) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [Triangle.time]

/-- The nonnegative part, as a closed subspace of the original toric space. -/
def positivePart : Set Space := {x | modulus x = x}

abbrev PositivePart := positivePart

theorem positivePart_isClosed : IsClosed positivePart :=
  isClosed_eq modulus_continuous continuous_id

/-- In each actual affine chart the positive part is precisely the ordinary
nonnegative real orthant. -/
@[simp] theorem inclusion_mem_positivePart_iff (s : Triangle) (z : CoordinateSpace 3) :
    inclusion s z ∈ positivePart ↔ z ∈ nonnegativeCoordinates := by
  change modulus (inclusion s z) = inclusion s z ↔ _
  rw [modulus_inclusion, (inclusion_openEmbedding s).injective.eq_iff,
    coordinateModulus_eq_self_iff]

/-- The positive real torus inside the reference dense toric chart. -/
def positiveTorus : Set Space := inclusion referenceTriangle '' positiveCoordinates

theorem positiveTorus_eq_modulus_image_openTorus :
    positiveTorus = modulus '' openTorus := by
  rw [positiveTorus, positiveCoordinates_eq_modulus_image_torus, openTorus,
    image_image, image_image]
  congr 1
  funext z
  exact (modulus_inclusion referenceTriangle z).symm

@[simp] theorem modulus_mem_positivePart (x : Space) : modulus x ∈ positivePart :=
  modulus_idempotent x

theorem range_modulus : Set.range modulus = positivePart := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact modulus_mem_positivePart y
  · intro hx
    exact ⟨x, hx⟩

theorem positiveTorus_subset_positivePart : positiveTorus ⊆ positivePart := by
  rw [positiveTorus_eq_modulus_image_openTorus, ← range_modulus]
  exact image_subset_range _ _

/-- This identifies the fixed locus with the source's definition of the
nonnegative toric space: the closure of the positive real torus. -/
theorem closure_positiveTorus : closure positiveTorus = positivePart := by
  apply le_antisymm
  · exact closure_minimal positiveTorus_subset_positivePart positivePart_isClosed
  · intro x hx
    rw [positiveTorus_eq_modulus_image_openTorus, ← hx]
    exact mem_closure_image modulus_continuous.continuousAt (openTorus_dense x)

/-- The modulus retraction has the actual subspace topology as its codomain. -/
def modulusRetraction (x : Space) : PositivePart :=
  ⟨modulus x, modulus_mem_positivePart x⟩

@[simp] theorem modulusRetraction_coe (x : Space) :
    (modulusRetraction x : Space) = modulus x := rfl

theorem modulusRetraction_continuous : Continuous modulusRetraction :=
  modulus_continuous.subtype_mk _

@[simp] theorem modulusRetraction_subtype_val (x : PositivePart) :
    modulusRetraction (x : Space) = x :=
  Subtype.ext x.property

theorem modulusRetraction_leftInverse :
    Function.LeftInverse modulusRetraction (Subtype.val : PositivePart → Space) :=
  modulusRetraction_subtype_val

/-- The genuine compact real torus acting on the toric space. -/
abbrev CompactTorus := Fin 3 → Circle

def compactTorusUnits : CompactTorus →* ActingTorus where
  toFun u i := Circle.toUnits (u i)
  map_one' := by
    funext i
    exact Circle.toUnits.map_one
  map_mul' u v := by
    funext i
    exact Circle.toUnits.map_mul (u i) (v i)

@[simp] theorem compactTorusUnits_apply (u : CompactTorus) (i : Fin 3) :
    (compactTorusUnits u i : ℂ) = (u i : ℂ) := rfl

theorem compactTorusUnits_continuous : Continuous compactTorusUnits := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  have h : Continuous (fun u : CompactTorus => (u i : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact ⟨h, h.inv₀ (fun u => (u i).coe_ne_zero)⟩

def compactTorusAction (u : CompactTorus) (x : Space) : Space :=
  torusAction (compactTorusUnits u) x

@[simp] theorem compactTorusAction_one (x : Space) : compactTorusAction 1 x = x := by
  simp [compactTorusAction]

theorem compactTorusAction_mul (u v : CompactTorus) (x : Space) :
    compactTorusAction u (compactTorusAction v x) = compactTorusAction (u * v) x := by
  simp [compactTorusAction, torusAction_mul]

instance compactTorusMulAction : MulAction CompactTorus Space where
  smul := compactTorusAction
  one_smul := compactTorusAction_one
  mul_smul u v x := (compactTorusAction_mul u v x).symm

theorem compactTorusAction_continuous :
    Continuous (fun p : CompactTorus × Space => compactTorusAction p.1 p.2) := by
  have h : Continuous (fun p : CompactTorus × Space => (compactTorusUnits p.1, p.2)) :=
    (compactTorusUnits_continuous.comp continuous_fst).prodMk continuous_snd
  change Continuous ((fun p : ActingTorus × Space => torusAction p.1 p.2) ∘
    (fun p : CompactTorus × Space => (compactTorusUnits p.1, p.2)))
  exact torusAction_joint_continuous.comp h

instance compactTorusContinuousSMul : ContinuousSMul CompactTorus Space :=
  ⟨compactTorusAction_continuous⟩

@[simp] theorem norm_factors_compactTorusUnits (s : Triangle) (u : CompactTorus)
    (i : Fin 3) : ‖factors s (compactTorusUnits u) i‖ = 1 := by
  simp [factors, monomial, norm_prod, norm_zpow, Circle.norm_coe]

theorem coordinateModulus_scale_compactTorusUnits (s : Triangle) (u : CompactTorus)
    (z : CoordinateSpace 3) :
    coordinateModulus (scale s (compactTorusUnits u) z) = coordinateModulus z := by
  funext i
  change (‖factors s (compactTorusUnits u) i * z i‖ : ℂ) = (‖z i‖ : ℂ)
  rw [norm_mul, norm_factors_compactTorusUnits, one_mul]

@[simp] theorem modulus_compactTorusAction (u : CompactTorus) (x : Space) :
    modulus (compactTorusAction u x) = modulus x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [compactTorusAction, coordinateModulus_scale_compactTorusUnits]

@[simp] theorem norm_time_compactTorusAction (u : CompactTorus) (x : Space) :
    ‖time (compactTorusAction u x)‖ = ‖time x‖ := by
  simp [compactTorusAction, time_torusAction, Circle.norm_coe]

/-- Coordinate polar decomposition, including the zero coordinates. The
inverse integral ray matrix converts coordinate phases to the acting torus. -/
theorem exists_unitNorm_scale_modulus (s : Triangle) (z : CoordinateSpace 3) :
    ∃ u : ActingTorus, (∀ i, ‖(u i : ℂ)‖ = 1) ∧
      scale s u (coordinateModulus z) = z := by
  classical
  have hphase (c : ℂ) : ∃ w : ℂ, ‖w‖ = 1 ∧ w * (‖c‖ : ℂ) = c := by
    by_cases hc : c = 0
    · exact ⟨1, norm_one, by simp [hc]⟩
    · refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hc)]
      · exact div_mul_cancel₀ _ (by simpa only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
          using hc)
  choose w hw hmul using fun i => hphase (z i)
  have hw0 : w ∈ torus := by
    intro i hi
    have h := hw i
    rw [hi, norm_zero] at h
    exact zero_ne_one h
  let u : ActingTorus := fun i =>
    Units.mk0 (monomial s.rays w i) (monomial_mapsTo_torus s.rays hw0 i)
  have hu : ∀ i, ‖(u i : ℂ)‖ = 1 := by
    intro i
    change ‖monomial s.rays w i‖ = 1
    simp only [monomial, norm_prod, norm_zpow, hw, one_zpow, Finset.prod_const_one]
  refine ⟨u, hu, ?_⟩
  have hf : factors s u = w := by
    change monomial s.dual (monomial s.rays w) = w
    rw [monomial_mul_on_torus _ _ hw0, dual_rays, monomial_one]
  ext i
  change factors s u i * (‖z i‖ : ℂ) = z i
  rw [hf]
  exact hmul i

theorem exists_compactTorus_scale_modulus (s : Triangle) (z : CoordinateSpace 3) :
    ∃ u : CompactTorus, scale s (compactTorusUnits u) (coordinateModulus z) = z := by
  obtain ⟨u, hu, hz⟩ := exists_unitNorm_scale_modulus s z
  let v : CompactTorus := fun i =>
    ⟨(u i : ℂ), mem_sphere_zero_iff_norm.mpr (hu i)⟩
  refine ⟨v, ?_⟩
  have hv : compactTorusUnits v = u := by
    funext i
    apply Units.ext
    rfl
  rw [hv]
  exact hz

theorem exists_compactTorusAction_modulus (x : Space) :
    ∃ u : CompactTorus, compactTorusAction u (modulus x) = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨u, hu⟩ := exists_compactTorus_scale_modulus s z
  refine ⟨u, ?_⟩
  change torusAction (compactTorusUnits u) (modulus (inclusion s z)) = inclusion s z
  rw [modulus_inclusion, torusAction_inclusion, hu]

/-- The multiplication map in the polar description of the actual toric space. -/
def polarMultiplication (p : CompactTorus × PositivePart) : Space :=
  compactTorusAction p.1 p.2

theorem polarMultiplication_continuous : Continuous polarMultiplication := by
  have h : Continuous (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  change Continuous ((fun p : CompactTorus × Space => compactTorusAction p.1 p.2) ∘
    (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))))
  exact compactTorusAction_continuous.comp h

@[simp] theorem modulus_polarMultiplication (p : CompactTorus × PositivePart) :
    modulus (polarMultiplication p) = p.2 := by
  change modulus (compactTorusAction p.1 p.2) = p.2
  rw [modulus_compactTorusAction]
  exact p.2.property

theorem polarMultiplication_surjective : Function.Surjective polarMultiplication := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactTorusAction_modulus x
  exact ⟨(u, modulusRetraction x), hu⟩

/-- The positive coordinate is unique; the only ambiguity is its actual
compact-torus stabilizer. -/
theorem polarMultiplication_eq_iff (p q : CompactTorus × PositivePart) :
    polarMultiplication p = polarMultiplication q ↔ p.2 = q.2 ∧
      p.1⁻¹ * q.1 ∈ MulAction.stabilizer CompactTorus (p.2 : Space) := by
  rcases p with ⟨u, x⟩
  rcases q with ⟨v, y⟩
  constructor
  · intro h
    have hxy : x = y := Subtype.ext (by simpa using congrArg modulus h)
    subst y
    refine ⟨rfl, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    change u • (x : Space) = v • (x : Space) at h
    rw [mul_smul, ← h, inv_smul_smul]
  · rintro ⟨hxy, h⟩
    change x = y at hxy
    subst y
    have hs := congrArg (fun z : Space => u • z) (MulAction.mem_stabilizer_iff.mp h)
    change u • (x : Space) = v • (x : Space)
    simpa only [smul_smul, mul_inv_cancel_left] using hs.symm

/-- Away from the central fibre every compact-torus phase is uniquely
determined by its action. -/
theorem compactTorusAction_injective_of_time_ne_zero {x : Space} (hx : time x ≠ 0) :
    Function.Injective (fun u : CompactTorus => compactTorusAction u x) := by
  intro u v huv
  have hxt : x ∈ openTorus := (mem_openTorus_iff x).mpr hx
  have he := congrArg torusCoordinates huv
  change torusCoordinates (torusAction (compactTorusUnits u) x) =
    torusCoordinates (torusAction (compactTorusUnits v) x) at he
  rw [torusCoordinates_action _ hxt, torusCoordinates_action _ hxt] at he
  funext i
  apply Circle.ext
  exact mul_right_cancel₀ (torusCoordinates_nonzero hxt i) (congrFun he i)

/-- The action is a shear on the product, so its projection is closed by
compactness of the real torus. -/
def compactTorusActionShear : CompactTorus × Space ≃ₜ CompactTorus × Space where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk continuous_smul
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.smul continuous_snd)

theorem compactTorusAction_isClosedMap :
    IsClosedMap (fun p : CompactTorus × Space => compactTorusAction p.1 p.2) :=
  isClosedMap_snd_of_compactSpace.comp compactTorusActionShear.isClosedMap

theorem compactTorusAction_isProperMap :
    IsProperMap (fun p : CompactTorus × Space => compactTorusAction p.1 p.2) :=
  isProperMap_snd_of_compactSpace.comp compactTorusActionShear.isProperMap

theorem polarMultiplication_isClosedMap : IsClosedMap polarMultiplication := by
  have h : IsClosedMap (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))) :=
    ((Homeomorph.refl CompactTorus).isClosedEmbedding.prodMap
      positivePart_isClosed.isClosedEmbedding_subtypeVal).isClosedMap
  change IsClosedMap ((fun p : CompactTorus × Space => compactTorusAction p.1 p.2) ∘
    (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))))
  exact compactTorusAction_isClosedMap.comp h

theorem polarMultiplication_isProperMap : IsProperMap polarMultiplication := by
  have h : IsProperMap (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))) :=
    ((Homeomorph.refl CompactTorus).isClosedEmbedding.prodMap
      positivePart_isClosed.isClosedEmbedding_subtypeVal).isProperMap
  change IsProperMap ((fun p : CompactTorus × Space => compactTorusAction p.1 p.2) ∘
    (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))))
  exact compactTorusAction_isProperMap.comp h

/-- The polar description is a quotient presentation of the original
topology, not a topology installed on an abstract set of phases. -/
theorem polarMultiplication_isQuotientMap : IsQuotientMap polarMultiplication :=
  polarMultiplication_isClosedMap.isQuotientMap
    polarMultiplication_continuous polarMultiplication_surjective

/-- The nonnegative part of the literal closed toric tube. -/
abbrev ClosedPositiveTube (η : ℝ) := {x : PositivePart // ‖time (x : Space)‖ ≤ η}

theorem closedPolarMap_mem_iff (η : ℝ) (p : CompactTorus × PositivePart) :
    polarMultiplication p ∈ {x : Space | ‖time x‖ ≤ η} ↔
      p.2 ∈ {x : PositivePart | ‖time (x : Space)‖ ≤ η} := by
  change ‖time (compactTorusAction p.1 p.2)‖ ≤ η ↔ ‖time (p.2 : Space)‖ ≤ η
  rw [norm_time_compactTorusAction]

/-- Polar multiplication restricted over the closed time disc. Its target
is definitionally the `ClosedTube` used for cusp straightening. -/
def closedPolarMap (η : ℝ) : CompactTorus × ClosedPositiveTube η →
    {x : Space // ‖time x‖ ≤ η} :=
  ProductRestriction.productRestriction polarMultiplication
    {x : PositivePart | ‖time (x : Space)‖ ≤ η} {x : Space | ‖time x‖ ≤ η}
    (closedPolarMap_mem_iff η)

@[simp] theorem closedPolarMap_coe (η : ℝ) (p : CompactTorus × ClosedPositiveTube η) :
    (closedPolarMap η p : Space) = compactTorusAction p.1 (p.2.1 : Space) := rfl

theorem closedPolarMap_continuous (η : ℝ) : Continuous (closedPolarMap η) :=
  ProductRestriction.productRestriction_continuous _ _ _ _ polarMultiplication_continuous

theorem closedPolarMap_isClosedMap (η : ℝ) : IsClosedMap (closedPolarMap η) :=
  ProductRestriction.productRestriction_isClosedMap _ _ _ _ polarMultiplication_isClosedMap

theorem closedPolarMap_isProperMap (η : ℝ) : IsProperMap (closedPolarMap η) :=
  ProductRestriction.productRestriction_isProperMap _ _ _ _ polarMultiplication_isProperMap

theorem closedPolarMap_surjective (η : ℝ) : Function.Surjective (closedPolarMap η) :=
  ProductRestriction.productRestriction_surjective _ _ _ _ polarMultiplication_surjective

theorem closedPolarMap_isQuotientMap (η : ℝ) : IsQuotientMap (closedPolarMap η) :=
  (closedPolarMap_isClosedMap η).isQuotientMap
    (closedPolarMap_continuous η) (closedPolarMap_surjective η)

/-- The modulus also retracts the literal closed tube onto its positive part. -/
def closedModulusRetraction (η : ℝ) (x : {x : Space // ‖time x‖ ≤ η}) :
    ClosedPositiveTube η :=
  ⟨modulusRetraction x, by
    change ‖time (modulus (x : Space))‖ ≤ η
    simpa only [time_modulus, Complex.norm_real, norm_norm] using x.property⟩

@[simp] theorem closedModulusRetraction_coe (η : ℝ)
    (x : {x : Space // ‖time x‖ ≤ η}) :
    ((closedModulusRetraction η x).1 : Space) = modulus (x : Space) := rfl

theorem closedModulusRetraction_continuous (η : ℝ) :
    Continuous (closedModulusRetraction η) :=
  (modulusRetraction_continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem closedModulusRetraction_closedPolarMap (η : ℝ)
    (p : CompactTorus × ClosedPositiveTube η) :
    closedModulusRetraction η (closedPolarMap η p) = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  change modulus (compactTorusAction p.1 (p.2.1 : Space)) = (p.2.1 : Space)
  rw [modulus_compactTorusAction]
  exact p.2.1.property

theorem closedPolarMap_eq_iff (η : ℝ) (p q : CompactTorus × ClosedPositiveTube η) :
    closedPolarMap η p = closedPolarMap η q ↔ p.2 = q.2 ∧
      p.1⁻¹ * q.1 ∈ MulAction.stabilizer CompactTorus (p.2.1 : Space) := by
  constructor
  · intro h
    have hval : polarMultiplication (p.1, p.2.1) =
        polarMultiplication (q.1, q.2.1) :=
      congrArg (fun x : {x : Space // ‖time x‖ ≤ η} => (x : Space)) h
    have he := (polarMultiplication_eq_iff (p.1, p.2.1) (q.1, q.2.1)).mp hval
    exact ⟨Subtype.ext he.1, he.2⟩
  · rintro ⟨hpq, hstab⟩
    apply Subtype.ext
    change polarMultiplication (p.1, p.2.1) = polarMultiplication (q.1, q.2.1)
    exact (polarMultiplication_eq_iff _ _).mpr ⟨congrArg Subtype.val hpq, hstab⟩

end Wikipedia.HopfProblem.ToricSpace
