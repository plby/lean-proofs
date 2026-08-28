import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# Scalar transitions of an arbitrary native complex line bundle

The cover and transition functions are extracted from the native bundle's
own trivializations. No global trivialization or presentation by factors is
assumed. Evaluating a complex-linear coordinate change at `1` gives its
nonzero scalar; the ordinary vector-bundle cocycle identity gives the scalar
cocycle identity.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative

open HolomorphicCharacterBundle

variable {M : Type*} [TopologicalSpace M] (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

/-- The bundle's existing preferred local trivialization. -/
abbrev nativeTriv (i : M) : Trivialization ℂ (π ℂ V) :=
  trivializationAt ℂ V i

/-- A native complex-linear coordinate change is multiplication by its value
at `1`, including the harmless identity definition outside the overlap. -/
theorem coordChange_apply (i j x : M) (c : ℂ) :
    (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x c =
      (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x 1 * c := by
  let e := (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x
  change e c = e 1 * c
  calc
    e c = e (c • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    _ = c • e 1 := e.map_smul c 1
    _ = e 1 * c := mul_comm _ _

theorem coordChange_one_ne_zero (i j x : M) :
    (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x 1 ≠ 0 := by
  intro h
  have hz := ((nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x).injective
    (h.trans (map_zero _).symm)
  exact one_ne_zero hz

/-- The actual nonzero scalar coordinate change, with no choices of logarithms. -/
def scalarTransition (i j x : M) : ℂˣ :=
  Units.mk0 ((nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x 1)
    (coordChange_one_ne_zero V i j x)

@[simp] theorem scalarTransition_coe (i j x : M) :
    (scalarTransition V i j x : ℂ) =
      (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x 1 := rfl

theorem scalarTransition_self (i x : M) (hx : x ∈ (nativeTriv V i).baseSet) :
    scalarTransition V i i x = 1 := by
  apply Units.ext
  change (nativeTriv V i).coordChangeL ℂ (nativeTriv V i) x 1 = 1
  rw [Trivialization.coordChangeL_apply _ _ ⟨hx, hx⟩]
  exact ((nativeTriv V i).linearEquivAt ℂ x hx).apply_symm_apply 1

theorem coordChange_comp (i j k x : M)
    (hx : x ∈ (nativeTriv V i).baseSet ∩ (nativeTriv V j).baseSet ∩
      (nativeTriv V k).baseSet) (c : ℂ) :
    (nativeTriv V j).coordChangeL ℂ (nativeTriv V k) x
      ((nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x c) =
        (nativeTriv V i).coordChangeL ℂ (nativeTriv V k) x c := by
  rw [Trivialization.coe_coordChangeL _ _ ⟨hx.1.2, hx.2⟩,
    Trivialization.coe_coordChangeL _ _ hx.1,
    Trivialization.coe_coordChangeL _ _ ⟨hx.1.1, hx.2⟩]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem scalarTransition_comp (i j k x : M)
    (hx : x ∈ (nativeTriv V i).baseSet ∩ (nativeTriv V j).baseSet ∩
      (nativeTriv V k).baseSet) :
    scalarTransition V j k x * scalarTransition V i j x =
      scalarTransition V i k x := by
  apply Units.ext
  change _ * _ = _
  rw [scalarTransition_coe, scalarTransition_coe, scalarTransition_coe,
    ← coordChange_apply V]
  exact coordChange_comp V i j k x hx 1

theorem scalarTransition_continuousOn (i j : M) :
    ContinuousOn (fun x => (scalarTransition V i j x : ℂ))
      ((nativeTriv V i).baseSet ∩ (nativeTriv V j).baseSet) :=
  (continuousOn_coordChange (R := ℂ) (nativeTriv V i) (nativeTriv V j)).clm_apply
    continuousOn_const

/-- The scalar cocycle on the original native trivializing cover. -/
def data : TransitionData M M where
  baseSet i := (nativeTriv V i).baseSet
  isOpen_baseSet i := (nativeTriv V i).open_baseSet
  indexAt := id
  mem_baseSet_at := FiberBundle.mem_baseSet_trivializationAt ℂ V
  transition := scalarTransition V
  transition_self := scalarTransition_self V
  transition_comp := scalarTransition_comp V
  continuousOn_transition := scalarTransition_continuousOn V

@[simp] theorem data_baseSet (i : M) :
    (data V).baseSet i = (nativeTriv V i).baseSet := rfl

@[simp] theorem data_indexAt (x : M) : (data V).indexAt x = x := rfl

@[simp] theorem data_transition (i j x : M) :
    (data V).transition i j x = scalarTransition V i j x := rfl

theorem core_coordChange_eq_native (i j x : M) (c : ℂ) :
    (data V).core.coordChange i j x c =
      (nativeTriv V i).coordChangeL ℂ (nativeTriv V j) x c :=
  (coordChange_apply V i j x c).symm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [ContMDiffVectorBundle ω ℂ V I]

/-- Analyticity follows from the original native `ContMDiffVectorBundle`
instance by evaluating its operator-valued transition function at `1`. -/
theorem scalarTransition_holomorphic (i j : M) :
    ContMDiffOn I (modelWithCornersSelf ℂ ℂ) ω
      (fun x => (scalarTransition V i j x : ℂ))
      ((nativeTriv V i).baseSet ∩ (nativeTriv V j).baseSet) :=
  (contMDiffOn_coordChangeL (IB := I) (nativeTriv V i) (nativeTriv V j)).clm_apply
    contMDiffOn_const

instance data_isHolomorphic : (data V).IsHolomorphic I where
  contMDiffOn_transition := scalarTransition_holomorphic V I

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative
