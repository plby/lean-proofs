import Wikipedia.HopfProblem.HolomorphicPicardNativeGluingCore

/-!
# Product coordinates from an actual compatible nonzero section

Continuous nonzero scalar coordinates on the original covering sets,
compatible with the original unit cocycle, specify a fibrewise product
coordinate on the original native cocycle bundle. The coordinate formulas
below hold in every original local trivialization. Continuity is established
separately using those unchanged trivializations and their native topology.
-/

noncomputable section

open Bundle Set TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicPicard.ContinuousCore

open HolomorphicPicardNative HolomorphicExponentialSheaf
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M) (hU : ∀ x : M, ∃ i : ι, x ∈ U i)
  (c : CechOneCocycle (unitsSheaf I M) U)
  (a : ∀ i : ι, C(U i, ℂ))

local notation "D" => cocycleTransitionData I M U hU c
local notation "Z" => cocycleCore I M U hU c

/-- The section coordinate in the original core's preferred chart. -/
def preferredCoordinate (x : M) : ℂ :=
  a ((D).indexAt x) ⟨x, (D).mem_baseSet_at x⟩

variable (hne : ∀ i (x : U i), a i x ≠ 0)
  (hcompat : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j),
    unitSectionEval (c.value i j) ⟨x, hi, hj⟩ * a i ⟨x, hi⟩ = a j ⟨x, hj⟩)

include hne in
theorem preferredCoordinate_ne_zero (x : M) :
    preferredCoordinate I M U hU c a x ≠ 0 := hne _ _

include hcompat in
/-- Compatibility expressed in the original native transition data. -/
theorem transition_preferredCoordinate (i : ι) (x : M) (hi : x ∈ U i) :
    ((D).transition ((D).indexAt x) i x : ℂ) *
        preferredCoordinate I M U hU c a x = a i ⟨x, hi⟩ := by
  rw [cocycleTransitionData_transition I M U hU c _ i x
    ⟨(D).mem_baseSet_at x, hi⟩]
  exact hcompat _ i x ((D).mem_baseSet_at x) hi

/-- Divide an original native fibre vector by the chosen nonzero section. -/
def toProduct (p : (Z).TotalSpace) : M × ℂ :=
  (p.proj, id (α := ℂ) p.2 / preferredCoordinate I M U hU c a p.proj)

/-- Multiply a product coordinate by the same original nonzero section. -/
def fromProduct (p : M × ℂ) : (Z).TotalSpace :=
  ⟨p.1, preferredCoordinate I M U hU c a p.1 * p.2⟩

@[simp] theorem toProduct_fst (p : (Z).TotalSpace) :
    (toProduct I M U hU c a p).1 = p.proj := rfl

@[simp] theorem fromProduct_proj (p : M × ℂ) :
    (fromProduct I M U hU c a p).proj = p.1 := rfl

include hne hcompat in
/-- The forward coordinate agrees with division in every original local chart. -/
theorem toProduct_snd_localTriv (i : ι) (p : (Z).TotalSpace)
    (hi : p.proj ∈ U i) :
    (toProduct I M U hU c a p).2 =
      ((Z).localTriv i p).2 / a i ⟨p.proj, hi⟩ := by
  change id (α := ℂ) p.2 / preferredCoordinate I M U hU c a p.proj =
    (((D).transition ((D).indexAt p.proj) i p.proj : ℂ) * id (α := ℂ) p.2) /
      a i ⟨p.proj, hi⟩
  apply (div_eq_div_iff (preferredCoordinate_ne_zero I M U hU c a hne p.proj)
    (hne i ⟨p.proj, hi⟩)).mpr
  rw [← transition_preferredCoordinate I M U hU c a hcompat i p.proj hi]
  ring

include hcompat in
/-- The inverse coordinate has the original section's scalar in every chart. -/
theorem fromProduct_localTriv (i : ι) (p : M × ℂ) (hi : p.1 ∈ U i) :
    (Z).localTriv i (fromProduct I M U hU c a p) =
      (p.1, a i ⟨p.1, hi⟩ * p.2) := by
  change (p.1, ((D).transition ((D).indexAt p.1) i p.1 : ℂ) *
    (preferredCoordinate I M U hU c a p.1 * p.2)) = _
  rw [← mul_assoc, transition_preferredCoordinate I M U hU c a hcompat i p.1 hi]

include hne in
theorem fromProduct_toProduct (p : (Z).TotalSpace) :
    fromProduct I M U hU c a (toProduct I M U hU c a p) = p := by
  cases p with
  | mk x v =>
    change (⟨x, preferredCoordinate I M U hU c a x *
      (id (α := ℂ) v / preferredCoordinate I M U hU c a x)⟩ : (Z).TotalSpace) = ⟨x, v⟩
    congr 1
    field_simp [preferredCoordinate_ne_zero I M U hU c a hne x]
    rfl

include hne in
theorem toProduct_fromProduct (p : M × ℂ) :
    toProduct I M U hU c a (fromProduct I M U hU c a p) = p := by
  apply Prod.ext
  · rfl
  change (preferredCoordinate I M U hU c a p.1 * p.2) /
    preferredCoordinate I M U hU c a p.1 = p.2
  exact mul_div_cancel_left₀ _ (preferredCoordinate_ne_zero I M U hU c a hne p.1)

end Wikipedia.HopfProblem.HolomorphicPicard.ContinuousCore
