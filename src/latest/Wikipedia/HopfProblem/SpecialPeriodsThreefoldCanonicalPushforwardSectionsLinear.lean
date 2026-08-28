import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsBasic

/-!
# Pointwise linear operations on native holomorphic bundle sections

Addition and the scalar actions are the original fibre operations.
Their holomorphicity is checked in the original bundle charts, not
transported through an equivalence with scalar functions.  Literal
restriction is complex-linear and semilinear over restriction of the
holomorphic scalar functions.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
    (C : VectorBundleCore ℂ M ℂ ι)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [C.IsContMDiff I ω]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

namespace Section

instance instZero (U : Opens M) : Zero (Section C I U) :=
  ⟨⟨fun _ => 0, (Bundle.contMDiff_zeroSection ℂ C.Fiber).comp contMDiff_subtype_val⟩⟩

instance instAdd (U : Opens M) : Add (Section C I U) where
  add s t := ⟨fun x => s x + t x, by
    intro x
    let i := C.indexAt (x : M)
    have hx : (x : M) ∈ C.baseSet i := C.mem_baseSet_at x
    apply (holomorphicAt_iff C I _ x i hx).mpr
    have hs := (holomorphicAt_iff C I s x i hx).mp (s.contMDiff_toFun x)
    have ht := (holomorphicAt_iff C I t x i hx).mp (t.contMDiff_toFun x)
    apply (hs.add ht).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt
      ((C.isOpen_baseSet i).mem_nhds hx)] with y hy
    exact ((C.localTriv i).linear ℂ hy).1 (s y) (t y)⟩

instance instNeg (U : Opens M) : Neg (Section C I U) where
  neg s := ⟨fun x => -s x, by
    intro x
    let i := C.indexAt (x : M)
    have hx : (x : M) ∈ C.baseSet i := C.mem_baseSet_at x
    apply (holomorphicAt_iff C I _ x i hx).mpr
    have hs := (holomorphicAt_iff C I s x i hx).mp (s.contMDiff_toFun x)
    apply hs.neg.congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt
      ((C.isOpen_baseSet i).mem_nhds hx)] with y hy
    exact ((C.localTriv i).linear ℂ hy).map_neg (s y)⟩

instance instSub (U : Opens M) : Sub (Section C I U) := ⟨fun s t => s + -t⟩

omit [C.IsContMDiff I ω] in
@[simp] theorem zero_apply (U : Opens M) (x : U) : (0 : Section C I U) x = 0 := rfl

@[simp] theorem add_apply {U : Opens M} (s t : Section C I U) (x : U) :
    (s + t) x = s x + t x := rfl

@[simp] theorem neg_apply {U : Opens M} (s : Section C I U) (x : U) :
    (-s) x = -s x := rfl

@[simp] theorem sub_apply {U : Opens M} (s t : Section C I U) (x : U) :
    (s - t) x = s x - t x := (sub_eq_add_neg _ _).symm

omit [C.IsContMDiff I ω] in
private theorem coe_zero (U : Opens M) :
    ((0 : Section C I U) : ∀ x : U, C.Fiber (x : M)) = 0 := rfl

private theorem coe_add {U : Opens M} (s t : Section C I U) :
    (s + t : Section C I U).toFun = s.toFun + t.toFun := rfl

private theorem coe_neg {U : Opens M} (s : Section C I U) :
    (-s : Section C I U).toFun = -s.toFun := rfl

private theorem coe_sub {U : Opens M} (s t : Section C I U) :
    (s - t : Section C I U).toFun = s.toFun - t.toFun := by
  funext x
  exact sub_apply C I s t x

instance instNSMul (U : Opens M) : SMul ℕ (Section C I U) := ⟨nsmulRec⟩

private theorem coe_nsmul {U : Opens M} (s : Section C I U) (k : ℕ) :
    (k • s : Section C I U).toFun = k • s.toFun := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

instance instZSMul (U : Opens M) : SMul ℤ (Section C I U) := ⟨zsmulRec⟩

private theorem coe_zsmul {U : Opens M} (s : Section C I U) (k : ℤ) :
    (k • s : Section C I U).toFun = k • s.toFun := by
  rcases k with n | n
  · exact (coe_nsmul C I s n).trans (by simp only [Int.ofNat_eq_natCast, natCast_zsmul])
  · exact (congrArg Neg.neg (coe_nsmul C I s (n + 1))).trans (by simp only [negSucc_zsmul])

/-- The group laws hold for the literal pointwise fibre operations. -/
instance instAddCommGroup (U : Opens M) : AddCommGroup (Section C I U) :=
  (coe_injective C I U).addCommGroup _ (coe_zero C I U) (coe_add C I)
    (coe_neg C I) (coe_sub C I) (coe_nsmul C I) (coe_zsmul C I)

@[simp] theorem nsmul_apply {U : Opens M} (k : ℕ) (s : Section C I U) (x : U) :
    (k • s) x = k • s x := congrFun (coe_nsmul C I s k) x

@[simp] theorem zsmul_apply {U : Opens M} (k : ℤ) (s : Section C I U) (x : U) :
    (k • s) x = k • s x := congrFun (coe_zsmul C I s k) x

/-- Holomorphic scalar functions act on each original bundle fibre. -/
instance instFunctionSMul (U : Opens M) :
    SMul (HolomorphicFunctionSheaf.Section I M U) (Section C I U) where
  smul f s := ⟨fun x => f x • s x, by
    intro x
    let i := C.indexAt (x : M)
    have hx : (x : M) ∈ C.baseSet i := C.mem_baseSet_at x
    apply (holomorphicAt_iff C I _ x i hx).mpr
    have hs := (holomorphicAt_iff C I s x i hx).mp (s.contMDiff_toFun x)
    apply ((f.contMDiff x).smul hs).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt
      ((C.isOpen_baseSet i).mem_nhds hx)] with y hy
    exact ((C.localTriv i).linear ℂ hy).2 (f y) (s y)⟩

@[simp] theorem function_smul_apply {U : Opens M}
    (f : HolomorphicFunctionSheaf.Section I M U) (s : Section C I U) (x : U) :
    (f • s) x = f x • s x := rfl

/-- The module over actual holomorphic functions, with its pointwise action. -/
instance instFunctionModule (U : Opens M) :
    Module (HolomorphicFunctionSheaf.Section I M U) (Section C I U) where
  one_smul s := by ext x; exact one_smul ℂ (s x)
  mul_smul f g s := by ext x; exact mul_smul (f x) (g x) (s x)
  smul_zero f := by ext x; exact smul_zero (f x)
  smul_add f s t := by ext x; exact smul_add (f x) (s x) (t x)
  add_smul f g s := by ext x; exact add_smul (f x) (g x) (s x)
  zero_smul s := by ext x; exact zero_smul ℂ (s x)

/-- Complex constants act by scalar multiplication in each original fibre. -/
instance instComplexSMul (U : Opens M) : SMul ℂ (Section C I U) where
  smul c s := ⟨fun x => c • s x, by
    intro x
    let i := C.indexAt (x : M)
    have hx : (x : M) ∈ C.baseSet i := C.mem_baseSet_at x
    apply (holomorphicAt_iff C I _ x i hx).mpr
    have hs := (holomorphicAt_iff C I s x i hx).mp (s.contMDiff_toFun x)
    have hc : ContMDiffAt I I₁ ω (fun _ : U => c) x := contMDiffAt_const
    apply (hc.smul hs).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt
      ((C.isOpen_baseSet i).mem_nhds hx)] with y hy
    exact ((C.localTriv i).linear ℂ hy).2 c (s y)⟩

@[simp] theorem complex_smul_apply {U : Opens M}
    (c : ℂ) (s : Section C I U) (x : U) : (c • s) x = c • s x := rfl

/-- The genuine constant-scalar complex vector-space structure. -/
instance instComplexModule (U : Opens M) : Module ℂ (Section C I U) where
  one_smul s := by ext x; exact one_smul ℂ (s x)
  mul_smul c d s := by ext x; exact mul_smul c d (s x)
  smul_zero c := by ext x; exact smul_zero c
  smul_add c s t := by ext x; exact smul_add c (s x) (t x)
  add_smul c d s := by ext x; exact add_smul c d (s x)
  zero_smul s := by ext x; exact zero_smul ℂ (s x)

instance instScalarTower (U : Opens M) :
    IsScalarTower ℂ (HolomorphicFunctionSheaf.Section I M U) (Section C I U) where
  smul_assoc c f s := by
    ext x
    exact smul_assoc c (f x) (s x)

instance instSMulCommClass (U : Opens M) :
    SMulCommClass ℂ (HolomorphicFunctionSheaf.Section I M U) (Section C I U) where
  smul_comm c f s := by
    ext x
    exact smul_comm c (f x) (s x)

omit [C.IsContMDiff I ω] in
@[simp] theorem restrict_zero {U V : Opens M} (h : U ≤ V) :
    restrict C I h (0 : Section C I V) = 0 := by ext x; rfl

@[simp] theorem restrict_add {U V : Opens M} (h : U ≤ V) (s t : Section C I V) :
    restrict C I h (s + t) = restrict C I h s + restrict C I h t := by ext x; rfl

@[simp] theorem restrict_neg {U V : Opens M} (h : U ≤ V) (s : Section C I V) :
    restrict C I h (-s) = -restrict C I h s := by ext x; rfl

@[simp] theorem restrict_sub {U V : Opens M} (h : U ≤ V) (s t : Section C I V) :
    restrict C I h (s - t) = restrict C I h s - restrict C I h t := by ext x; rfl

/-- Restriction acts on the scalar function by the original scalar restriction. -/
theorem restrict_function_smul {U V : Opens M} (h : U ≤ V)
    (f : HolomorphicFunctionSheaf.Section I M V) (s : Section C I V) :
    restrict C I h (f • s) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M h f • restrict C I h s := by
  ext x
  rfl

@[simp] theorem restrict_complex_smul {U V : Opens M} (h : U ≤ V)
    (c : ℂ) (s : Section C I V) :
    restrict C I h (c • s) = c • restrict C I h s := by ext x; rfl

/-- Literal restriction as an additive homomorphism. -/
def restrictionAddHom {U V : Opens M} (h : U ≤ V) :
    Section C I V →+ Section C I U where
  toFun := restrict C I h
  map_zero' := restrict_zero C I h
  map_add' := restrict_add C I h

@[simp] theorem restrictionAddHom_apply {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) : restrictionAddHom C I h s = restrict C I h s := rfl

/-- Literal restriction as a complex-linear map. -/
def restrictionLinearMap {U V : Opens M} (h : U ≤ V) :
    Section C I V →ₗ[ℂ] Section C I U where
  __ := restrictionAddHom C I h
  map_smul' := restrict_complex_smul C I h

@[simp] theorem restrictionLinearMap_apply {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) : restrictionLinearMap C I h s = restrict C I h s := rfl

/-- Restriction is semilinear over restriction of the actual holomorphic functions. -/
def restrictionSemilinearMap {U V : Opens M} (h : U ≤ V) :
    Section C I V →ₛₗ[(HolomorphicFunctionSheaf.restrictionAlgHom I M h).toRingHom]
      Section C I U where
  __ := restrictionAddHom C I h
  map_smul' := restrict_function_smul C I h

@[simp] theorem restrictionSemilinearMap_apply {U V : Opens M} (h : U ≤ V)
    (s : Section C I V) : restrictionSemilinearMap C I h s = restrict C I h s := rfl

@[simp] theorem restrictionAddHom_refl (U : Opens M) :
    restrictionAddHom C I (le_refl U) = AddMonoidHom.id (Section C I U) := by
  ext s x
  rfl

theorem restrictionAddHom_comp {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W) :
    (restrictionAddHom C I hUV).comp (restrictionAddHom C I hVW) =
      restrictionAddHom C I (hUV.trans hVW) := by
  ext s x
  rfl

@[simp] theorem restrictionLinearMap_refl (U : Opens M) :
    restrictionLinearMap C I (le_refl U) = LinearMap.id := by
  ext s x
  rfl

theorem restrictionLinearMap_comp {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W) :
    (restrictionLinearMap C I hUV).comp (restrictionLinearMap C I hVW) =
      restrictionLinearMap C I (hUV.trans hVW) := by
  ext s x
  rfl

end Section

end Wikipedia.HopfProblem.NativeBundleSections
