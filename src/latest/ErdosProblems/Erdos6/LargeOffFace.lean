import ErdosProblems.Erdos6.LargeFiberLower

/-!
# Generic coordinate-one/off-face reindexing

The constructions are polymorphic in the finite shift set, so the elaborator
never needs to reduce the concrete cardinal `2^512`.
-/

namespace Erdos6.Maynard

open scoped BigOperators

noncomputable section

def tupleOffFace (H : Finset ℕ) (m : H) : Finset ℕ := H.erase m.1

def tupleOffFaceRestriction {H : Finset ℕ} (m : H)
    (r : H → ℕ) : tupleOffFace H m → ℕ :=
  fun h => r ⟨h.1, (Finset.mem_erase.mp h.2).2⟩

def tupleOffFaceExtension {H : Finset ℕ} (m : H)
    (u : tupleOffFace H m → ℕ) : H → ℕ :=
  fun h => if hh : h = m then 1 else
    u ⟨h.1, Finset.mem_erase.mpr ⟨by
      intro hval
      exact hh (Subtype.ext hval), h.2⟩⟩

@[simp] theorem tupleOffFaceExtension_at {H : Finset ℕ}
    (m : H) (u : tupleOffFace H m → ℕ) :
    tupleOffFaceExtension m u m = 1 := by
  simp [tupleOffFaceExtension]

theorem tupleOffFaceExtension_off {H : Finset ℕ}
    (m : H) (u : tupleOffFace H m → ℕ)
    (h : H) (hh : h ≠ m) :
    tupleOffFaceExtension m u h =
      u ⟨h.1, Finset.mem_erase.mpr ⟨by
        intro hval
        exact hh (Subtype.ext hval), h.2⟩⟩ := by
  simp [tupleOffFaceExtension, hh]

@[simp] theorem tupleOffFaceRestriction_extension {H : Finset ℕ}
    (m : H) (u : tupleOffFace H m → ℕ) :
    tupleOffFaceRestriction m (tupleOffFaceExtension m u) = u := by
  funext h
  unfold tupleOffFaceRestriction
  have hh : (⟨h.1, (Finset.mem_erase.mp h.2).2⟩ : H) ≠ m := by
    intro heq
    exact (Finset.mem_erase.mp h.2).1
      (congrArg (fun z : H => z.1) heq)
  rw [tupleOffFaceExtension_off _ _ _ hh]

theorem tupleOffFaceExtension_restriction {H : Finset ℕ}
    (m : H) (r : H → ℕ) (hrm : r m = 1) :
    tupleOffFaceExtension m (tupleOffFaceRestriction m r) = r := by
  funext h
  by_cases hh : h = m
  · subst h
    simp [hrm]
  · rw [tupleOffFaceExtension_off m _ h hh]
    rfl

def coordinateOneTupleEquiv {H : Finset ℕ} (m : H) :
    (tupleOffFace H m → ℕ) ≃ {r : H → ℕ // r m = 1} where
  toFun u := ⟨tupleOffFaceExtension m u, tupleOffFaceExtension_at m u⟩
  invFun r := tupleOffFaceRestriction m r.1
  left_inv u := tupleOffFaceRestriction_extension m u
  right_inv r := by
    apply Subtype.ext
    exact tupleOffFaceExtension_restriction m r.1 r.2

def eraseSubtypeEquiv {H : Finset ℕ} (m : H) :
    (Finset.univ.erase m : Finset H) ≃ tupleOffFace H m where
  toFun h :=
    ⟨h.1.1, Finset.mem_erase.mpr ⟨by
      intro hv
      exact (Finset.mem_erase.mp h.2).1 (Subtype.ext hv), h.1.2⟩⟩
  invFun h :=
    ⟨⟨h.1, (Finset.mem_erase.mp h.2).2⟩,
      Finset.mem_erase.mpr ⟨by
        intro heq
        exact (Finset.mem_erase.mp h.2).1
          (congrArg (fun z : H => z.1) heq), Finset.mem_univ _⟩⟩
  left_inv h := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv h := by apply Subtype.ext; rfl

theorem prod_subtype_erase_eq_offFace
    {H : Finset ℕ} {M : Type*} [CommMonoid M] (m : H) (f : H → M) :
    (∏ h ∈ (Finset.univ : Finset H).erase m, f h) =
      ∏ h : tupleOffFace H m,
        f ⟨h.1, (Finset.mem_erase.mp h.2).2⟩ := by
  rw [← Finset.prod_coe_sort]
  apply Fintype.prod_equiv (eraseSubtypeEquiv m)
  intro h
  rfl

theorem maynardS2OffCoordinateProduct_extension
    {H : Finset ℕ} (m : H) (u : tupleOffFace H m → ℕ) :
    BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m
        (tupleOffFaceExtension m u) =
      BoundedGaps.Maynard.divisorTupleProduct (tupleOffFace H m) u := by
  unfold BoundedGaps.Maynard.maynardS2OffCoordinateProduct
    BoundedGaps.Maynard.divisorTupleProduct
  rw [prod_subtype_erase_eq_offFace]
  apply Finset.prod_congr rfl
  intro h hh
  have hne : (⟨h.1, (Finset.mem_erase.mp h.2).2⟩ : H) ≠ m := by
    intro heq
    exact (Finset.mem_erase.mp h.2).1
      (congrArg (fun z : H => z.1) heq)
  rw [tupleOffFaceExtension_off _ _ _ hne]

theorem divisorTupleProduct_extension
    {H : Finset ℕ} (m : H) (u : tupleOffFace H m → ℕ) :
    BoundedGaps.Maynard.divisorTupleProduct H (tupleOffFaceExtension m u) =
      BoundedGaps.Maynard.divisorTupleProduct (tupleOffFace H m) u := by
  rw [BoundedGaps.Maynard.divisorTupleProduct_eq_offCoordinateProduct m
    (tupleOffFaceExtension_at m u)]
  exact maynardS2OffCoordinateProduct_extension m u

theorem isMaynardDivisorTuple_extension_iff
    {H : Finset ℕ} (R W : ℕ) (m : H) (u : tupleOffFace H m → ℕ) :
    BoundedGaps.Maynard.IsMaynardDivisorTuple H R W
        (tupleOffFaceExtension m u) ↔
      BoundedGaps.Maynard.IsMaynardDivisorTuple (tupleOffFace H m) R W u := by
  unfold BoundedGaps.Maynard.IsMaynardDivisorTuple
  rw [divisorTupleProduct_extension]

theorem extension_mem_support_iff
    {H : Finset ℕ} (R W : ℕ) (m : H) (u : tupleOffFace H m → ℕ) :
    tupleOffFaceExtension m u ∈
        BoundedGaps.Maynard.maynardDivisorTupleSupport H R W ↔
      u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
        (tupleOffFace H m) R W := by
  rw [BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff,
    BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff]
  constructor
  · intro h
    have hu := (isMaynardDivisorTuple_extension_iff R W m u).mp h.2
    exact ⟨hu.mem_maynardDivisorTupleBox, hu⟩
  · intro h
    have hf := (isMaynardDivisorTuple_extension_iff R W m u).mpr h.2
    exact ⟨hf.mem_maynardDivisorTupleBox, hf⟩

theorem sum_coordinateOneSupport_eq_offFace
    {H : Finset ℕ} {M : Type*} [AddCommMonoid M]
    (R W : ℕ) (m : H) (F : (H → ℕ) → M) :
    (∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport H R W).filter
        (fun r => r m = 1), F r) =
      ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
          (tupleOffFace H m) R W,
        F (tupleOffFaceExtension m u) := by
  apply Finset.sum_bij (fun r _ => tupleOffFaceRestriction m r)
  · intro r hr
    have hrData := Finset.mem_filter.mp hr
    have hext := tupleOffFaceExtension_restriction m r hrData.2
    apply (extension_mem_support_iff R W m
      (tupleOffFaceRestriction m r)).mp
    simpa [hext] using hrData.1
  · intro r hr s hs heq
    have hrm := (Finset.mem_filter.mp hr).2
    have hsm := (Finset.mem_filter.mp hs).2
    calc
      r = tupleOffFaceExtension m (tupleOffFaceRestriction m r) :=
        (tupleOffFaceExtension_restriction m r hrm).symm
      _ = tupleOffFaceExtension m (tupleOffFaceRestriction m s) := by rw [heq]
      _ = s := tupleOffFaceExtension_restriction m s hsm
  · intro u hu
    let r := tupleOffFaceExtension m u
    have hr : r ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W :=
      (extension_mem_support_iff R W m u).mpr hu
    refine ⟨r, Finset.mem_filter.mpr
      ⟨hr, tupleOffFaceExtension_at m u⟩, ?_⟩
    exact tupleOffFaceRestriction_extension m u
  · intro r hr
    exact congrArg F
      (tupleOffFaceExtension_restriction m r (Finset.mem_filter.mp hr).2).symm

theorem tupleOffFace_largePowerTuple (m : largePowerTuple) :
    tupleOffFace largePowerTuple m = largeOffFace m := rfl

theorem update_mem_support_of_mem_coordinateFiber
    {H : Finset ℕ} {R W u : ℕ} (m : H) {r : H → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W r)
    (hrm : r m = 1)
    (hu : u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
      H R W m r) :
    Function.update r m u ∈
      BoundedGaps.Maynard.maynardDivisorTupleSupport H R W :=
  (BoundedGaps.Maynard.update_mem_maynardDivisorTupleSupport_iff
    m hr hrm u).mpr hu

theorem normalizedLog_mem_finiteSimplex_of_mem_support
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ} (hR : 1 < R)
    (hd : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W) :
    BoundedGaps.Maynard.normalizedDivisorLogTuple H R d ∈
      BoundedGaps.Maynard.finiteSimplexOf H := by
  have hdata :=
    BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_cube_and_sum_lt_one_of_mem_support
      hR hd
  refine ⟨?_, hdata.2.le⟩
  rw [BoundedGaps.Maynard.maynardCubeOf, Set.mem_pi]
  intro h hh
  exact hdata.1 h

end

end Erdos6.Maynard
