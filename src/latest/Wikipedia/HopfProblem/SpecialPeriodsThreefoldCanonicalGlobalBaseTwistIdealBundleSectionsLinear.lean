import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwistIdealBundleSections

/-!
# Pointwise module structure on actual holomorphic bundle sections

All operations are defined directly in the original fibres. Their
holomorphicity is checked in the original local trivializations. On a
trivializing subopen, the native coefficient equivalence is linear over
the ring of holomorphic functions on that subopen.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist.IdealBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
    (A : HolomorphicCharacterBundle.TransitionData M ι)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

namespace Section

private theorem holomorphicAt_iff {U : Opens M}
    (s : ∀ y : U, A.core.Fiber (y : M)) (x : U) (i : ι)
    (hx : (x : M) ∈ A.baseSet i) :
    ContMDiffAt I (I.prod I₁) ω (fun y : U => (⟨(y : M), s y⟩ : A.core.TotalSpace)) x ↔
      ContMDiffAt I I₁ ω (fun y : U => (A.core.localTriv i ⟨(y : M), s y⟩).2) x := by
  rw [(A.core.localTriv i).contMDiffAt_iff
    (f := fun y : U => (⟨(y : M), s y⟩ : A.core.TotalSpace))
    (show (⟨(x : M), s x⟩ : A.core.TotalSpace) ∈ (A.core.localTriv i).source from hx)]
  exact and_iff_right (contMDiff_subtype_val x)

instance instZero (U : Opens M) : Zero (Section A I U) :=
  ⟨⟨fun _ => 0, (Bundle.contMDiff_zeroSection ℂ A.core.Fiber).comp contMDiff_subtype_val⟩⟩

instance instAdd (U : Opens M) : Add (Section A I U) where
  add s t := ⟨fun x => s x + t x, by
    intro x
    let i := A.indexAt (x : M)
    have hx : (x : M) ∈ A.baseSet i := A.mem_baseSet_at x
    apply (holomorphicAt_iff A I _ x i hx).mpr
    have hs := (holomorphicAt_iff A I s x i hx).mp (s.contMDiff_toFun x)
    have ht := (holomorphicAt_iff A I t x i hx).mp (t.contMDiff_toFun x)
    apply (hs.add ht).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt
      ((A.isOpen_baseSet i).mem_nhds hx)] with y hy
    exact ((A.core.localTriv i).linear ℂ hy).1 (s y) (t y)⟩

instance instNeg (U : Opens M) : Neg (Section A I U) where
  neg s := ⟨fun x => -s x, by
    intro x
    let i := A.indexAt (x : M)
    have hx : (x : M) ∈ A.baseSet i := A.mem_baseSet_at x
    apply (holomorphicAt_iff A I _ x i hx).mpr
    have hs := (holomorphicAt_iff A I s x i hx).mp (s.contMDiff_toFun x)
    apply hs.neg.congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt
      ((A.isOpen_baseSet i).mem_nhds hx)] with y hy
    exact ((A.core.localTriv i).linear ℂ hy).map_neg (s y)⟩

instance instSub (U : Opens M) : Sub (Section A I U) := ⟨fun s t => s + -t⟩

omit [A.IsHolomorphic I] in
@[simp] theorem zero_apply (U : Opens M) (x : U) : (0 : Section A I U) x = 0 := rfl

@[simp] theorem add_apply {U : Opens M} (s t : Section A I U) (x : U) :
    (s + t) x = s x + t x := rfl

@[simp] theorem neg_apply {U : Opens M} (s : Section A I U) (x : U) :
    (-s) x = -s x := rfl

@[simp] theorem sub_apply {U : Opens M} (s t : Section A I U) (x : U) :
    (s - t) x = s x - t x := (sub_eq_add_neg _ _).symm

omit [A.IsHolomorphic I] in
private theorem coe_injective (U : Opens M) :
    Function.Injective (fun s : Section A I U => s.toFun) := by
  intro s t h
  exact Section.ext A I (congrFun h)

omit [A.IsHolomorphic I] in
private theorem coe_zero (U : Opens M) :
    ((0 : Section A I U) : ∀ x : U, A.core.Fiber (x : M)) = 0 := rfl

private theorem coe_add {U : Opens M} (s t : Section A I U) :
    (s + t : Section A I U).toFun = s.toFun + t.toFun := rfl

private theorem coe_neg {U : Opens M} (s : Section A I U) :
    (-s : Section A I U).toFun = -s.toFun := rfl

private theorem coe_sub {U : Opens M} (s t : Section A I U) :
    (s - t : Section A I U).toFun = s.toFun - t.toFun := by
  funext x
  exact sub_apply A I s t x

instance instNSMul (U : Opens M) : SMul ℕ (Section A I U) := ⟨nsmulRec⟩

private theorem coe_nsmul {U : Opens M} (s : Section A I U) (k : ℕ) :
    (k • s : Section A I U).toFun = k • s.toFun := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

instance instZSMul (U : Opens M) : SMul ℤ (Section A I U) := ⟨zsmulRec⟩

private theorem coe_zsmul {U : Opens M} (s : Section A I U) (k : ℤ) :
    (k • s : Section A I U).toFun = k • s.toFun := by
  rcases k with n | n
  · exact (coe_nsmul A I s n).trans (by simp only [Int.ofNat_eq_natCast, natCast_zsmul])
  · exact (congrArg Neg.neg (coe_nsmul A I s (n + 1))).trans (by simp only [negSucc_zsmul])

/-- The group operations are the literal pointwise fibre operations. -/
instance instAddCommGroup (U : Opens M) : AddCommGroup (Section A I U) :=
  (coe_injective A I U).addCommGroup _ (coe_zero A I U) (coe_add A I)
    (coe_neg A I) (coe_sub A I) (coe_nsmul A I) (coe_zsmul A I)

/-- A holomorphic function acts pointwise on each original bundle fibre. -/
instance instFunctionSMul (U : Opens M) :
    SMul (HolomorphicFunctionSheaf.Section I M U) (Section A I U) where
  smul f s := ⟨fun x => f x • s x, by
    intro x
    let i := A.indexAt (x : M)
    have hx : (x : M) ∈ A.baseSet i := A.mem_baseSet_at x
    apply (holomorphicAt_iff A I _ x i hx).mpr
    have hs := (holomorphicAt_iff A I s x i hx).mp (s.contMDiff_toFun x)
    apply ((f.contMDiff x).smul hs).congr_of_eventuallyEq
    filter_upwards [continuous_subtype_val.continuousAt
      ((A.isOpen_baseSet i).mem_nhds hx)] with y hy
    exact ((A.core.localTriv i).linear ℂ hy).2 (f y) (s y)⟩

@[simp] theorem function_smul_apply {U : Opens M}
    (f : HolomorphicFunctionSheaf.Section I M U) (s : Section A I U) (x : U) :
    (f • s) x = f x • s x := rfl

/-- Actual holomorphic bundle sections form a module over holomorphic functions. -/
instance instFunctionModule (U : Opens M) :
    Module (HolomorphicFunctionSheaf.Section I M U) (Section A I U) where
  one_smul s := by ext x; exact one_smul ℂ (s x)
  mul_smul f g s := by ext x; exact mul_smul (f x) (g x) (s x)
  smul_zero f := by ext x; exact smul_zero (f x)
  smul_add f s t := by ext x; exact smul_add (f x) (s x) (t x)
  add_smul f g s := by ext x; exact add_smul (f x) (g x) (s x)
  zero_smul s := by ext x; exact zero_smul ℂ (s x)

omit [A.IsHolomorphic I] in
@[simp] theorem restrict_zero {U V : Opens M} (h : U ≤ V) :
    restrict A I h (0 : Section A I V) = 0 := by ext x; rfl

@[simp] theorem restrict_add {U V : Opens M} (h : U ≤ V) (s t : Section A I V) :
    restrict A I h (s + t) = restrict A I h s + restrict A I h t := by ext x; rfl

/-- Restriction respects the action through literal restriction of the scalar function. -/
theorem restrict_function_smul {U V : Opens M} (h : U ≤ V)
    (f : HolomorphicFunctionSheaf.Section I M V) (s : Section A I V) :
    restrict A I h (f • s) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M h f • restrict A I h s := by
  ext x
  rfl

end Section

@[simp] theorem coefficientEquiv_add (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (s t : Section A I U) :
    coefficientEquiv A I i U hU (s + t) =
      coefficientEquiv A I i U hU s + coefficientEquiv A I i U hU t := by
  ext x
  exact ((A.core.localTriv i).linear ℂ (hU x x.property)).1 (s x) (t x)

@[simp] theorem coefficientEquiv_function_smul (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (s : Section A I U) :
    coefficientEquiv A I i U hU (f • s) = f • coefficientEquiv A I i U hU s := by
  ext x
  exact ((A.core.localTriv i).linear ℂ (hU x x.property)).2 (f x) (s x)

/-- The native coefficient equivalence is linear over the holomorphic function ring. -/
def coefficientLinearEquiv (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ A.baseSet i) :
    Section A I U ≃ₗ[HolomorphicFunctionSheaf.Section I M U]
      HolomorphicFunctionSheaf.Section I M U where
  __ := coefficientEquiv A I i U hU
  map_add' := coefficientEquiv_add A I i U hU
  map_smul' := coefficientEquiv_function_smul A I i U hU

@[simp] theorem coefficientLinearEquiv_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (s : Section A I U) (x : U) :
    coefficientLinearEquiv A I i U hU s x =
      (A.core.localTriv i ⟨(x : M), s x⟩).2 := rfl

@[simp] theorem coefficientLinearEquiv_symm_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    (coefficientLinearEquiv A I i U hU).symm f x =
      (A.core.localTriv i).symm (x : M) (f x) := rfl

theorem coefficientLinearEquiv_restrict (i : ι) {U V : Opens M} (h : U ≤ V)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (hV : ∀ x ∈ V, x ∈ A.baseSet i)
    (s : Section A I V) :
    coefficientLinearEquiv A I i U hU (Section.restrict A I h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M h
        (coefficientLinearEquiv A I i V hV s) := by
  ext x
  rfl

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist.IdealBundleSections
