import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreTrivialization

/-!
# The native zeroth-power bundle is the product bundle

The zeroth-power cocycle has constant unit transitions. Its constant
preferred-fibre value `1` is therefore a nowhere-zero holomorphic section
of the original total space. The native section trivialization identifies
that actual bundle with the product, with identity fibre coordinates.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)

/-- The actual constant preferred-fibre frame in the zeroth-power bundle. -/
def zeroPowerFrame (x : M) : (A.power 0).core.Fiber x := (1 : ℂ)

@[simp] theorem zeroPowerFrame_apply (x : M) :
    zeroPowerFrame A x = (1 : ℂ) := rfl

theorem zeroPowerFrame_ne_zero (x : M) : zeroPowerFrame A x ≠ 0 :=
  (one_ne_zero : (1 : ℂ) ≠ 0)

/-- Every original zero-power chart reads the frame as the constant `1`. -/
@[simp] theorem zeroPowerFrame_localCoefficient (i : ι) (x : M) :
    (A.power 0).localCoefficient (zeroPowerFrame A) i x = 1 := by
  change (A.transition (A.indexAt x) i x : ℂ) ^ 0 * (1 : ℂ) = 1
  simp only [pow_zero, one_mul]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Holomorphicity is proved in the native preferred charts, using only
that the zeroth-power transitions equal `1`. -/
theorem zeroPowerFrame_holomorphic :
    ContMDiff I (I.prod I₁) ω
      (fun x => (⟨x, zeroPowerFrame A x⟩ : (A.power 0).core.TotalSpace)) := by
  intro x
  rw [Bundle.contMDiffAt_section]
  change ContMDiffAt I I₁ ω
    (fun y : M => (A.transition (A.indexAt y) (A.indexAt x) y : ℂ) ^ 0 * (1 : ℂ)) x
  simpa only [pow_zero, one_mul] using
    (contMDiffAt_const : ContMDiffAt I I₁ ω (fun _ : M => (1 : ℂ)) x)

variable [A.IsHolomorphic I]

/-- The actual analytic product trivialization determined by the native
constant frame of the zeroth-power bundle. -/
def zeroPowerTrivialization :
    Diffeomorph (I.prod I₁) (I.prod I₁) (A.power 0).core.TotalSpace (M × ℂ) ω :=
  (A.power 0).sectionTrivialization (zeroPowerFrame A) I
    (zeroPowerFrame_holomorphic A I) (zeroPowerFrame_ne_zero A)

@[simp] theorem zeroPowerTrivialization_apply (p : (A.power 0).core.TotalSpace) :
    zeroPowerTrivialization A I p = (p.proj, id (α := ℂ) p.2) := by
  change (p.proj, (1 : ℂ)⁻¹ * id (α := ℂ) p.2) = _
  simp only [inv_one, one_mul]

@[simp] theorem zeroPowerTrivialization_symm_apply (p : M × ℂ) :
    (zeroPowerTrivialization A I).symm p = ⟨p.1, p.2⟩ := by
  change (⟨p.1, (1 : ℂ) * p.2⟩ : (A.power 0).core.TotalSpace) = _
  rw [one_mul]

@[simp] theorem zeroPowerTrivialization_fst (p : (A.power 0).core.TotalSpace) :
    (zeroPowerTrivialization A I p).1 = p.proj := rfl

@[simp] theorem zeroPowerTrivialization_symm_proj (p : M × ℂ) :
    ((zeroPowerTrivialization A I).symm p).proj = p.1 := rfl

@[simp] theorem zeroPowerTrivialization_snd (p : (A.power 0).core.TotalSpace) :
    (zeroPowerTrivialization A I p).2 = id (α := ℂ) p.2 := by
  rw [zeroPowerTrivialization_apply]

@[simp] theorem zeroPowerTrivialization_symm_snd (p : M × ℂ) :
    id (α := ℂ) ((zeroPowerTrivialization A I).symm p).2 = p.2 := by
  change (1 : ℂ) * p.2 = p.2
  exact one_mul p.2

theorem zeroPowerTrivialization_add (x : M) (v w : (A.power 0).core.Fiber x) :
    (zeroPowerTrivialization A I ⟨x, v + w⟩).2 =
      (zeroPowerTrivialization A I ⟨x, v⟩).2 +
        (zeroPowerTrivialization A I ⟨x, w⟩).2 := by
  simp only [zeroPowerTrivialization_snd]
  rfl

theorem zeroPowerTrivialization_smul (x : M) (c : ℂ) (v : (A.power 0).core.Fiber x) :
    (zeroPowerTrivialization A I ⟨x, c • v⟩).2 =
      c • (zeroPowerTrivialization A I ⟨x, v⟩).2 := by
  simp only [zeroPowerTrivialization_snd]
  rfl

@[simp] theorem zeroPowerTrivialization_frame (x : M) :
    zeroPowerTrivialization A I ⟨x, zeroPowerFrame A x⟩ = (x, 1) := by
  simp only [zeroPowerTrivialization_apply, zeroPowerFrame_apply]
  rfl

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
