import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBranchLocal
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# Analytic restriction maps for actual period families

Equality of the period functions makes the identity on real torus
coordinates holomorphic after a holomorphic change of base.  The proof
uses the actual complex-vector covering maps defining the period-family
atlases.  A local biholomorphism of bases gives a local biholomorphism of
the total spaces; no analytic structure is transported along a real
trivialization.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

local instance coveringChartedSpace {A : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] : ChartedSpace (ℂ × ComplexPlane₂) (A × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (A × ComplexPlane₂))

local instance coveringManifold {A : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [IsManifold I₁ ω A] :
    IsManifold IF ω (A × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) A ComplexPlane₂

section LocalDescent

variable {E F K M N T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    [TopologicalSpace T] [ChartedSpace K T]
    {q : M → N} {f : N → T} {x : M}

/-- A local biholomorphism can be cancelled on the source side of a
commuting covering square, using its actual local inverse. -/
theorem localDiffeomorphAt_of_comp
    (hq : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) ω q x)
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ K) ω (f ∘ q) x) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ F)
      (modelWithCornersSelf ℂ K) ω f (q x) := by
  have hx : hq.localInverse (q x) = x :=
    hq.localInverse_left_inv hq.localInverse_mem_target
  have hf' : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ K) ω (f ∘ q) (hq.localInverse (q x)) := by
    rw [hx]
    exact hf
  have h := hq.localInverse_isLocalDiffeomorphAt.comp
    (K := modelWithCornersSelf ℂ K) (P := T) hf'
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq h
  filter_upwards [hq.localInverse_eventuallyEq_right] with y hy
  change f y = f (q (hq.localInverse y))
  rw [show q (hq.localInverse y) = y from hy]

end LocalDescent

section Product

variable {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B]

/-- The actual partial inverse chart on the base, with unchanged complex
fibre coordinates. -/
def productPartialDiffeomorph (e : PartialDiffeomorph I₁ I₁ A B ω) :
    PartialDiffeomorph IF IF (A × ComplexPlane₂) (B × ComplexPlane₂) ω where
  toPartialEquiv := (e.toOpenPartialHomeomorph.prod
    (OpenPartialHomeomorph.refl ComplexPlane₂)).toPartialEquiv
  open_source := e.open_source.prod isOpen_univ
  open_target := e.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    rw [modelWithCornersSelf_prod]
    exact (e.contMDiffOn_toFun.comp contMDiff_fst.contMDiffOn
      (fun _ hx => hx.1)).prodMk contMDiff_snd.contMDiffOn
  contMDiffOn_invFun := by
    rw [modelWithCornersSelf_prod]
    exact (e.contMDiffOn_invFun.comp contMDiff_fst.contMDiffOn
      (fun _ hx => hx.1)).prodMk contMDiff_snd.contMDiffOn

theorem productMap_isLocalDiffeomorph {f : A → B}
    (hf : IsLocalDiffeomorph I₁ I₁ ω f) :
    IsLocalDiffeomorph IF IF ω (fun x : A × ComplexPlane₂ => (f x.1, x.2)) := by
  intro x
  obtain ⟨e, hx, he⟩ := hf x.1
  refine ⟨productPartialDiffeomorph e, ⟨hx, mem_univ _⟩, ?_⟩
  intro y hy
  exact Prod.ext (he hy.1) rfl

end Product

section PeriodMaps

variable {A B : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω A] [IsManifold I₁ ω B]
    (Q : HolomorphicPeriodMap ℂ A) (P : HolomorphicPeriodMap ℂ B)
    (f : A → B) (hperiod : ∀ a, Q.point a = P.point (f a))

/-- The actual map on total spaces, with constant real torus coordinates. -/
def periodFamilyMap : Q.TotalSpace → P.TotalSpace := fun x => (f x.1, x.2)

include hperiod

omit [IsManifold I₁ ω A] [IsManifold I₁ ω B] in
theorem periodFamilyMap_cover (x : A × ComplexPlane₂) :
    periodFamilyMap Q P f (Q.quotientMap x) = P.quotientMap (f x.1, x.2) := by
  apply Prod.ext
  · rfl
  · change standardLattice.mkQ ((Q.periodEquiv x.1).symm x.2) =
      standardLattice.mkQ ((P.periodEquiv (f x.1)).symm x.2)
    rw [show Q.periodEquiv x.1 = P.periodEquiv (f x.1) by
      simp only [HolomorphicPeriodMap.periodEquiv, hperiod]]

theorem periodFamilyMap_holomorphic (hf : ContMDiff I₁ I₁ ω f) :
    letI := Q.totalChartedSpace
    letI := P.totalChartedSpace
    ContMDiff IF IF ω (periodFamilyMap Q P f) := by
  let := Q.totalChartedSpace
  let := P.totalChartedSpace
  let := Q.coveringAction
  apply CoveringQuotient.contMDiff_of_comp Q.quotientCoveringMap IF ω
  have hb : ContMDiff IF IF ω (fun x : A × ComplexPlane₂ => (f x.1, x.2)) := by
    rw [modelWithCornersSelf_prod]
    exact (hf.comp contMDiff_fst).prodMk contMDiff_snd
  exact (P.quotientMap_holomorphic.comp hb).congr
    (periodFamilyMap_cover Q P f hperiod)

theorem periodFamilyMap_isLocalDiffeomorph (hf : IsLocalDiffeomorph I₁ I₁ ω f) :
    letI := Q.totalChartedSpace
    letI := P.totalChartedSpace
    IsLocalDiffeomorph IF IF ω (periodFamilyMap Q P f) := by
  let := Q.totalChartedSpace
  let := P.totalChartedSpace
  let := Q.coveringAction
  have hQ : IsLocalDiffeomorph IF IF ω Q.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph Q.quotientCoveringMap
      Q.coveringAction_holomorphic
  have hP : IsLocalDiffeomorph IF IF ω P.quotientMap := by
    let := P.coveringAction
    exact CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap
      P.coveringAction_holomorphic
  intro y
  obtain ⟨x, rfl⟩ := Q.quotientMap_surjective y
  apply localDiffeomorphAt_of_comp (hQ x)
  have h := (productMap_isLocalDiffeomorph hf x).comp
    (K := IF) (P := P.TotalSpace) (hP (f x.1, x.2))
  exact isLocalDiffeomorphAt_congr_of_eventuallyEq h
    (Filter.Eventually.of_forall (periodFamilyMap_cover Q P f hperiod))

end PeriodMaps

section OpenRestriction

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold I₁ ω B] (P : HolomorphicPeriodMap ℂ B)
    (U : TopologicalSpace.Opens B)

/-- Restrict the actual period functions to an open base. -/
def restrictPeriods : HolomorphicPeriodMap ℂ U where
  point x := P.point x
  holomorphic_tau := P.holomorphic_tau.comp contMDiff_subtype_val
  holomorphic_mu := P.holomorphic_mu.comp contMDiff_subtype_val
  holomorphic_beta := P.holomorphic_beta.comp contMDiff_subtype_val

/-- The literal full preimage of an open base in the actual family. -/
def periodFamilyOpen : TopologicalSpace.Opens P.TotalSpace :=
  ⟨P.projection ⁻¹' (U : Set B), U.isOpen.preimage continuous_fst⟩

def restrictFamilyMap : (restrictPeriods P U).TotalSpace → periodFamilyOpen P U :=
  fun x => ⟨(x.1.1, x.2), x.1.2⟩

omit [IsManifold I₁ ω B] in
theorem restrictFamilyMap_bijective : Function.Bijective (restrictFamilyMap P U) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    exact Prod.ext (Subtype.ext (congrArg (fun z : B × RealTorus₄ => z.1) he))
      (congrArg (fun z : B × RealTorus₄ => z.2) he)
  · intro y
    exact ⟨(⟨y.1.1, y.2⟩, y.1.2), rfl⟩

theorem restrictFamilyMap_isLocalDiffeomorph :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    IsLocalDiffeomorph IF IF ω (restrictFamilyMap P U) := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact isLocalDiffeomorph_codRestrictOpens IF IF
    (periodFamilyMap_isLocalDiffeomorph (restrictPeriods P U) P Subtype.val
      (fun _ => rfl) (isLocalDiffeomorph_subtypeVal I₁ U))
    (periodFamilyOpen P U) (fun x => x.1.2)

/-- The covering atlas of the restricted periods agrees with the
inherited atlas on the actual open part of the original family. -/
def restrictFamilyBiholomorph :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    Diffeomorph IF IF (restrictPeriods P U).TotalSpace (periodFamilyOpen P U) ω := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact (restrictFamilyMap_isLocalDiffeomorph P U).diffeomorphOfBijective
    (restrictFamilyMap_bijective P U)

@[simp] theorem restrictFamilyBiholomorph_apply (x : (restrictPeriods P U).TotalSpace) :
    restrictFamilyBiholomorph P U x = ⟨(x.1.1, x.2), x.1.2⟩ := rfl

@[simp] theorem restrictFamilyBiholomorph_symm_apply (x : periodFamilyOpen P U) :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    (restrictFamilyBiholomorph P U).symm x = (⟨x.1.1, x.2⟩, x.1.2) := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  apply (restrictFamilyBiholomorph P U).injective
  exact (restrictFamilyBiholomorph P U).apply_symm_apply x

end OpenRestriction

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
