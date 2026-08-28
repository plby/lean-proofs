import Wikipedia.HopfProblem.EllipticEquivariantData
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothForward

/-!
# Smooth vector lifts of translations on the original elliptic cap

A real-coordinate displacement depending smoothly on the original disc
coordinate gives a translation on the original complex-vector cover.
The actual varying-period equivalence converts the displacement into a
complex vector.  The translation is jointly real smooth in its time and
point, and its exact formula commutes with the original lattice quotient.

All charts below are the inherited open-disc and ordinary product charts.
No finite cap quotient, covariance assumption, or new atlas is used.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods

local notation "I₁" => modelWithCornersSelf ℝ ℂ
local notation "I₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "IV" => modelWithCornersSelf ℝ RealCoordinates
local notation "IF" => modelWithCornersSelf ℝ FamilyModel
local notation "IT" => modelWithCornersSelf ℝ (ℝ × FamilyModel)
local notation "IC" => modelWithCornersSelf ℝ (ℂ × RealCoordinates)

/-- The original disc times complex-vector product atlas. -/
@[instance_reducible] def capVectorChartedSpace :
    ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

attribute [local instance] capVectorChartedSpace

/-- The ordinary real time-product atlas on the same complex-vector cover. -/
@[instance_reducible] def capTimeVectorChartedSpace :
    ChartedSpace (ℝ × FamilyModel) (ℝ × (Disc × ComplexPlane₂)) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ FamilyModel) (ℝ × (Disc × ComplexPlane₂)))

/-- The unchanged open-disc chart paired with the original real period coordinates. -/
@[instance_reducible] def capRealCoordinatesChartedSpace :
    ChartedSpace (ℂ × RealCoordinates) (Disc × RealCoordinates) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ RealCoordinates) (Disc × RealCoordinates))

attribute [local instance] capTimeVectorChartedSpace capRealCoordinatesChartedSpace

variable {j : Kind} (D : Equivariant.Data j) (c : Disc → RealCoordinates)

/-- Translation on the actual complex-vector cover, preserving its original base point. -/
def capVectorTranslation (s : ℝ) (p : Disc × ComplexPlane₂) : Disc × ComplexPlane₂ :=
  (p.1, p.2 + D.periods.periodEquiv p.1 (s • c p.1))

@[simp] theorem capVectorTranslation_fst (s : ℝ) (p : Disc × ComplexPlane₂) :
    (capVectorTranslation D c s p).1 = p.1 := rfl

@[simp] theorem capVectorTranslation_snd (s : ℝ) (p : Disc × ComplexPlane₂) :
    (capVectorTranslation D c s p).2 =
      p.2 + D.periods.periodEquiv p.1 (s • c p.1) := rfl

@[simp] theorem capVectorTranslation_zero (p : Disc × ComplexPlane₂) :
    capVectorTranslation D c 0 p = p := by
  simp only [capVectorTranslation, zero_smul, map_zero, add_zero]

/-- The literal time-addition law before passing to any quotient. -/
theorem capVectorTranslation_add (s t : ℝ) (p : Disc × ComplexPlane₂) :
    capVectorTranslation D c (s + t) p =
      capVectorTranslation D c s (capVectorTranslation D c t p) := by
  apply Prod.ext
  · rfl
  · change p.2 + D.periods.periodEquiv p.1 ((s + t) • c p.1) =
      (p.2 + D.periods.periodEquiv p.1 (t • c p.1)) +
        D.periods.periodEquiv p.1 (s • c p.1)
    rw [add_smul, map_add]
    abel

/-- Opposite real time is the exact left inverse on the original cover. -/
@[simp] theorem capVectorTranslation_neg_apply (s : ℝ) (p : Disc × ComplexPlane₂) :
    capVectorTranslation D c (-s) (capVectorTranslation D c s p) = p := by
  rw [← capVectorTranslation_add, neg_add_cancel, capVectorTranslation_zero]

/-- Opposite real time is also the exact right inverse. -/
@[simp] theorem capVectorTranslation_apply_neg (s : ℝ) (p : Disc × ComplexPlane₂) :
    capVectorTranslation D c s (capVectorTranslation D c (-s) p) = p := by
  rw [← capVectorTranslation_add, add_neg_cancel, capVectorTranslation_zero]

/-- A vanishing displacement fixes the original covering point for every real time. -/
theorem capVectorTranslation_eq_self_of_zero (s : ℝ) (p : Disc × ComplexPlane₂)
    (hp : c p.1 = 0) : capVectorTranslation D c s p = p := by
  simp only [capVectorTranslation, hp, smul_zero, map_zero, add_zero]

/-- The real-period formula keeps the original basis and the original base. -/
theorem capVectorTranslation_periodCoordinates (s : ℝ) (z : Disc) (x : RealCoordinates) :
    capVectorTranslation D c s (z, D.periods.periodEquiv z x) =
      (z, D.periods.periodEquiv z (x + s • c z)) := by
  simp only [capVectorTranslation, map_add]

/-- Exact compatibility with the native lattice quotient, including the actual displacement. -/
theorem capVectorTranslation_quotientMap (s : ℝ) (p : Disc × ComplexPlane₂) :
    D.periods.quotientMap (capVectorTranslation D c s p) =
      (p.1, (D.periods.quotientMap p).2 + standardLattice.mkQ (s • c p.1)) := by
  simp only [capVectorTranslation, HolomorphicPeriodMap.quotientMap, map_add,
    LinearEquiv.symm_apply_apply]

private theorem capVectorBase_contMDiff :
    ContMDiff IF I₁ ∞ (Prod.fst : Disc × ComplexPlane₂ → Disc) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

private theorem capVectorFibre_contMDiff :
    ContMDiff IF I₂ ∞ (Prod.snd : Disc × ComplexPlane₂ → ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

private theorem capVectorTime_contMDiff :
    ContMDiff IT 𝓘(ℝ, ℝ) ∞ (Prod.fst : ℝ × (Disc × ComplexPlane₂) → ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_fst

private theorem capVectorPoint_contMDiff :
    ContMDiff IT IF ∞
      (Prod.snd : ℝ × (Disc × ComplexPlane₂) → Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_snd

private theorem capRealSmul_contDiff :
    ContDiff ℝ ∞ (fun p : ℝ × RealCoordinates => p.1 • p.2) :=
  contDiff_fst.smul contDiff_snd

private theorem capVectorAdd_contDiff :
    ContDiff ℝ ∞ (fun p : ComplexPlane₂ × ComplexPlane₂ => p.1 + p.2) :=
  contDiff_fst.add contDiff_snd

variable {c}

private theorem capTimeBase_contMDiff :
    ContMDiff IT I₁ ∞ (fun q : ℝ × (Disc × ComplexPlane₂) => q.2.1) :=
  capVectorBase_contMDiff.comp capVectorPoint_contMDiff

private theorem capTimeFibre_contMDiff :
    ContMDiff IT I₂ ∞ (fun q : ℝ × (Disc × ComplexPlane₂) => q.2.2) :=
  capVectorFibre_contMDiff.comp capVectorPoint_contMDiff

private theorem capScaledCoordinates_contMDiff (hc : ContMDiff I₁ IV ∞ c) :
    ContMDiff IT IV ∞
      (fun q : ℝ × (Disc × ComplexPlane₂) => q.1 • c q.2.1) :=
  capRealSmul_contDiff.contMDiff.comp
    (capVectorTime_contMDiff.prodMk_space (hc.comp capTimeBase_contMDiff))

private theorem capPeriodInput_contMDiff (hc : ContMDiff I₁ IV ∞ c) :
    ContMDiff IT IC ∞
      (fun q : ℝ × (Disc × ComplexPlane₂) => (q.2.1, q.1 • c q.2.1)) := by
  rw [modelWithCornersSelf_prod]
  exact capTimeBase_contMDiff.prodMk (capScaledCoordinates_contMDiff hc)

private theorem capPeriodDisplacement_contMDiff (hc : ContMDiff I₁ IV ∞ c) :
    ContMDiff IT I₂ ∞
      (fun q : ℝ × (Disc × ComplexPlane₂) =>
        D.periods.periodEquiv q.2.1 (q.1 • c q.2.1)) := by
  change ContMDiff IT I₂ ∞
    ((fun x : Disc × RealCoordinates => D.periods.periodEquiv x.1 x.2) ∘
      (fun q : ℝ × (Disc × ComplexPlane₂) => (q.2.1, q.1 • c q.2.1)))
  exact (PeriodFamilyHolomorphicCohomology.Smooth.periodCoordinates_native_contMDiff
    (U := unitDisc) D.periods).comp (capPeriodInput_contMDiff hc)

private theorem capTranslatedFibre_contMDiff (hc : ContMDiff I₁ IV ∞ c) :
    ContMDiff IT I₂ ∞
      (fun q : ℝ × (Disc × ComplexPlane₂) =>
        q.2.2 + D.periods.periodEquiv q.2.1 (q.1 • c q.2.1)) :=
  capVectorAdd_contDiff.contMDiff.comp
    (capTimeFibre_contMDiff.prodMk_space (capPeriodDisplacement_contMDiff D hc))

/-- Joint smoothness in real time and the actual complex covering point. -/
theorem capVectorTranslation_joint_contMDiff (hc : ContMDiff I₁ IV ∞ c) :
    ContMDiff IT IF ∞
      (fun q : ℝ × (Disc × ComplexPlane₂) => capVectorTranslation D c q.1 q.2) := by
  rw [modelWithCornersSelf_prod]
  exact capTimeBase_contMDiff.prodMk (capTranslatedFibre_contMDiff D hc)

private theorem capFixedTimeSection_contMDiff (s : ℝ) :
    ContMDiff IF IT ∞ (fun p : Disc × ComplexPlane₂ => (s, p)) := by
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_const : ContMDiff IF 𝓘(ℝ, ℝ) ∞ (fun _ : Disc × ComplexPlane₂ => s)).prodMk
    (contMDiff_id : ContMDiff IF IF ∞ (fun p : Disc × ComplexPlane₂ => p))

/-- Every fixed-time translation is smooth for the same inherited covering atlas. -/
theorem capVectorTranslation_contMDiff (hc : ContMDiff I₁ IV ∞ c) (s : ℝ) :
    ContMDiff IF IF ∞ (capVectorTranslation D c s) := by
  exact (capVectorTranslation_joint_contMDiff D hc).comp (capFixedTimeSection_contMDiff s)

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
