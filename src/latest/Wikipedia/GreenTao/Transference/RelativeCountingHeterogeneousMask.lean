import Wikipedia.GreenTao.Transference.RelativeCountingDecoderTerminal

/-!
# Copy-dependent masks in relative counting

The two copies in a projected relative-counting correlation need not have
the same majorant.  This file allows a separate active-face mask

`active : Bool → Fin (n + 1) → Bool`

for each copy.  The corresponding Cauchy--Schwarz stage selector reads the
copy from the distinguished Boolean coordinate of a face vertex.  Thus a
face can retain the `false` copy of `ν`, the `true` copy, both copies, or
neither copy independently.

The stable stage and terminal decoders then give a full structural CFZ
certificate and the usual quantitative root bound.  The final specialization
uses `ν` on the `false` copy and the constant majorant one on the `true`
copy, which is the cross-copy case required by relative counting.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The copy-dependent AP cut system -/

/-- Copy-dependent AP face majorants. -/
def apCopyMaskedFaceMajorant
    {k N : ℕ}
    (ν : ZMod N → ℝ)
    (active : Bool → Fin k → Bool)
    (b : Bool) :
    Fin k → ZMod N → ℝ :=
  apMaskedFaceMajorant ν (active b)

@[simp]
theorem apCopyMaskedFaceMajorant_apply
    {k N : ℕ}
    (ν : ZMod N → ℝ)
    (active : Bool → Fin k → Bool)
    (b : Bool) (i : Fin k) (z : ZMod N) :
    apCopyMaskedFaceMajorant ν active b i z =
      if active b i then ν z else 1 :=
  rfl

/-- The exact two-copy cut system with an independent active mask on each
copy. -/
noncomputable def apTwoCopyHeterogeneousMaskedMajorizedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a => apTwoCopyCutTest n N g j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (apCopyMaskedFaceMajorant ν active) j a
  factor_nonneg := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (apCopyMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).1
  factor_le_majorant := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (apCopyMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).2

/-- The copy-dependent mask changes only the designated majorants, not the
represented centered correlation. -/
theorem apTwoCopyHeterogeneousMaskedMajorizedCutSystem_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        n N ν active g j hrest).form =
      apTwoCopyCenteredCorrelation n N ν g j := by
  unfold MajorizedCutSystem.form
  unfold apTwoCopyHeterogeneousMaskedMajorizedCutSystem
  unfold apTwoCopyCenteredCorrelation
  apply congrArg mean
  funext a
  apply congrArg mean
  funext y
  change
    apFaceCenteredCore n N ν j y *
        ∏ t,
          apTwoCopyCutTest n N g j a t
            (eraseCoordinate t y) =
      apFaceCenteredCore n N ν j y *
        ∏ b,
          apHeterogeneousIncidentProduct
            n N (g b) j (a b) y
  rw [prod_apTwoCopyCutTest_eraseCoordinate]

/-! ## Copy-aware recursive stage selectors -/

/-- At a paid Cauchy--Schwarz face, select a generated Boolean vertex
exactly when the copy read from its distinguished coordinate is active on
that face. -/
noncomputable def apCSHeterogeneousOrderedStageFaceExponent
    (r s : ℕ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1)) :
    LinearFormsExponent (((s + 1) + r) + 1) :=
  faceLinearFormsExponent
    (apCSOrderedStageCurrentFace r s j)
    (fun ω =>
      if ∃ bits : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits = ω
      then
        active
          (ω (apCSOrderedStageDistinguishedVertexIndex
            r s j))
          (apCSOrderedStageCurrentFace r s j)
      else false)

/-- Pointwise expansion of the copy-aware stage selector. -/
theorem linearFormsProduct_apCSHeterogeneousOrderedStageFaceExponent
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N) :
    linearFormsProduct (((s + 1) + r) + 1) N ν
        (apCSHeterogeneousOrderedStageFaceExponent
          r s active j) x =
      ∏ bits : Fin (r + 1) → Bool,
        if active (bits 0)
            (apCSOrderedStageCurrentFace r s j)
        then
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j bits) x)
        else 1 := by
  classical
  unfold apCSHeterogeneousOrderedStageFaceExponent
  rw [← faceSelectedProduct_eq_linearFormsProduct]
  unfold cubeSelectedProduct faceFactorFamily
  change
    (∏ ω : DeletedCube
        (((s + 1) + r) + 1)
        (apCSOrderedStageCurrentFace r s j),
      if
        (if ∃ bits : Fin (r + 1) → Bool,
            apCSOrderedStageVertex r s j bits = ω
          then
            active
              (ω (apCSOrderedStageDistinguishedVertexIndex
                r s j))
              (apCSOrderedStageCurrentFace r s j)
          else false)
      then
        ν (apLinearForm
          (((s + 1) + r) + 1) N
          (apCSOrderedStageCurrentFace r s j) ω x)
      else 1) = _
  have hpoint :
      ∀ ω : DeletedCube
          (((s + 1) + r) + 1)
          (apCSOrderedStageCurrentFace r s j),
        (if
          (if ∃ bits : Fin (r + 1) → Bool,
              apCSOrderedStageVertex r s j bits = ω
            then
              active
                (ω (apCSOrderedStageDistinguishedVertexIndex
                  r s j))
                (apCSOrderedStageCurrentFace r s j)
            else false)
        then
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j) ω x)
        else 1) =
          if ∃ bits : Fin (r + 1) → Bool,
              apCSOrderedStageVertex r s j bits = ω
          then
            if active
                (ω (apCSOrderedStageDistinguishedVertexIndex
                  r s j))
                (apCSOrderedStageCurrentFace r s j)
            then
              ν (apLinearForm
                (((s + 1) + r) + 1) N
                (apCSOrderedStageCurrentFace r s j) ω x)
            else 1
          else 1 := by
    intro ω
    by_cases hω :
        ∃ bits : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits = ω
    · simp [hω]
    · simp [hω]
  simp_rw [hpoint]
  rw [← Finset.prod_filter]
  rw [Finset.prod_subtype
    (p := fun ω :
      DeletedCube
        (((s + 1) + r) + 1)
        (apCSOrderedStageCurrentFace r s j) =>
      ∃ bits : Fin (r + 1) → Bool,
        apCSOrderedStageVertex r s j bits = ω)
    (Finset.univ.filter fun ω :
      DeletedCube
        (((s + 1) + r) + 1)
        (apCSOrderedStageCurrentFace r s j) =>
      ∃ bits : Fin (r + 1) → Bool,
        apCSOrderedStageVertex r s j bits = ω)
    (by simp)]
  symm
  apply Fintype.prod_equiv
    (apCSOrderedStageVertexEquiv r s j)
  intro bits
  change
    (if active (bits 0)
          (apCSOrderedStageCurrentFace r s j) then
        ν (apLinearForm
          (((s + 1) + r) + 1) N
          (apCSOrderedStageCurrentFace r s j)
          (apCSOrderedStageVertex r s j bits) x)
      else 1) =
      if active
          (apCSOrderedStageVertex r s j bits
            (apCSOrderedStageDistinguishedVertexIndex
              r s j))
          (apCSOrderedStageCurrentFace r s j)
      then
        ν (apLinearForm
          (((s + 1) + r) + 1) N
          (apCSOrderedStageCurrentFace r s j)
          (apCSOrderedStageVertex r s j bits) x)
      else 1
  rw [apCSOrderedStageVertex_distinguished]

/-! ## Copy-aware paid stage moments -/

/-- One original heterogeneous designated cut factor, evaluated on the
decoded stage tuple, is the product over the two copy choices at the
current face. -/
theorem apTwoCopyHeterogeneousMaskedMajorant_stageFactor
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (x : CubePoint (((s + 1) + r) + 1) N)
    (bits : Fin r → Bool) :
    (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest).majorant
        (apCSOrderedStageCubeEquiv r s N j x).1.1.base
        (csOrderedStageCurrentIndex r s)
        (csOrderedStageFactorInput r s
          (fun i =>
            selectPair
              ((apCSOrderedStageCubeEquiv
                r s N j x).1.1.pair i)
              (bits i))
          (apCSOrderedStageCubeEquiv
            r s N j x).1.2) =
      ∏ b : Bool,
        apCopyMaskedFaceMajorant ν active b
          (apCSOrderedStageCurrentFace r s j)
          (apLinearForm (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j
              (Fin.cons b bits)) x) := by
  let z :=
    csOrderedStageFactorInput r s
      (fun i =>
        selectPair
          ((apCSOrderedStageCubeEquiv
            r s N j x).1.1.pair i)
          (bits i))
      (apCSOrderedStageCubeEquiv
        r s N j x).1.2
  obtain ⟨y, hy⟩ :=
    exists_eraseCoordinate_eq
      (csOrderedStageCurrentIndex r s)
      (0 : ZMod N) z
  have hprocessed :
      (fun i =>
        selectPair
          ((apCSOrderedStageCubeEquiv
            r s N j x).1.1.pair i)
          (bits i)) =
        fun i =>
          x (j.succAbove
            (csOrderedStageProcessedIndex r s i))
            (bits i) := by
    funext i
    rw [apCSOrderedStageCubeEquiv_processedPair]
    cases bits i <;> rfl
  have hfuture :
      (apCSOrderedStageCubeEquiv
          r s N j x).1.2 =
        fun t =>
          x (j.succAbove
            (csOrderedStageFutureIndex r s t))
            false := by
    funext t
    exact apCSOrderedStageCubeEquiv_futureFalse
      r s N j x t
  have hz :
      z =
        csOrderedStageFactorInput r s
          (fun i =>
            x (j.succAbove
              (csOrderedStageProcessedIndex r s i))
              (bits i))
          (fun t =>
            x (j.succAbove
              (csOrderedStageFutureIndex r s t))
              false) := by
    unfold z
    exact congrArg₂
      (csOrderedStageFactorInput r s)
      hprocessed hfuture
  have hy' :
      eraseCoordinate
          (csOrderedStageCurrentIndex r s) y =
        csOrderedStageFactorInput r s
          (fun i =>
            x (j.succAbove
              (csOrderedStageProcessedIndex r s i))
              (bits i))
          (fun t =>
            x (j.succAbove
              (csOrderedStageFutureIndex r s t))
              false) :=
    hy.trans hz
  change
    apTwoCopyCutTest ((s + 1) + r) N
        (apCopyMaskedFaceMajorant ν active)
        j
        (apCSOrderedStageCubeEquiv
          r s N j x).1.1.base
        (csOrderedStageCurrentIndex r s) z =
      _
  rw [← hy]
  rw [apTwoCopyCutTest_eraseCoordinate]
  apply Fintype.prod_congr
  intro b
  rw [apCSOrderedStageCubeEquiv_base]
  apply congrArg
    (apCopyMaskedFaceMajorant ν active b
      (apCSOrderedStageCurrentFace r s j))
  exact
    apSimplexForm_eq_apLinearForm_csOrderedStageVertex
      r s N j x bits b y hy'

/-- The decoded paid majorant is exactly the copy-aware one-face CFZ
subproduct. -/
theorem iterNextDecoded_apTwoCopyHeterogeneousMasked_majorant_zero
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (x : CubePoint (((s + 1) + r) + 1) N) :
    (MajorizedCutSystem.iterNextDecoded
        (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
          ((s + 1) + r) N ν active g j hrest)).majorant
        ((apCSOrderedStageCubeEquiv
          r s N j x).1.1.base,
          (apCSOrderedStageCubeEquiv
            r s N j x).1.1.pair)
        0
        (apCSOrderedStageCubeEquiv
          r s N j x).1.2 =
      linearFormsProduct (((s + 1) + r) + 1) N ν
        (apCSHeterogeneousOrderedStageFaceExponent
          r s active j) x := by
  classical
  rw [
    MajorizedCutSystem.iterNextDecoded_majorant_zero]
  rw [
    linearFormsProduct_apCSHeterogeneousOrderedStageFaceExponent]
  simp_rw [
    apTwoCopyHeterogeneousMaskedMajorant_stageFactor]
  simp_rw [apCopyMaskedFaceMajorant_apply]
  let F : Bool → (Fin r → Bool) → ℝ :=
    fun b bits =>
      if active b
          (apCSOrderedStageCurrentFace r s j)
      then
        ν (apLinearForm
          (((s + 1) + r) + 1) N
          (apCSOrderedStageCurrentFace r s j)
          (apCSOrderedStageVertex r s j
            (Fin.cons b bits)) x)
      else 1
  have hreindex :
      (∏ bits : Fin (r + 1) → Bool,
        if active (bits 0)
            (apCSOrderedStageCurrentFace r s j)
        then
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j bits) x)
        else 1) =
        ∏ q : Bool × (Fin r → Bool),
          F q.1 q.2 := by
    apply Fintype.prod_equiv
      (Fin.consEquiv
        (fun _ : Fin (r + 1) => Bool)).symm
    intro bits
    rfl
  rw [hreindex, Fintype.prod_prod_type]
  rw [Finset.prod_comm]

/-- The decoded successor paid moment is an ordinary CFZ subproduct with
the copy-aware stage selector. -/
theorem iterNextDecoded_apTwoCopyHeterogeneousMasked_headMajorantMean
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    (MajorizedCutSystem.iterNextDecoded
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)).headMajorantMean =
      mean (linearFormsProduct
        (((s + 1) + r) + 1) N ν
        (apCSHeterogeneousOrderedStageFaceExponent
          r s active j)) := by
  rw [
    iterNextDecoded_headMajorantMean_eq_orderedCubeMean
      r s N j]
  apply congrArg mean
  funext x
  exact
    iterNextDecoded_apTwoCopyHeterogeneousMasked_majorant_zero
      r s N ν active g j hrest x

/-- The same paid-moment identity for the native nested `next` tower. -/
theorem iterNext_apTwoCopyHeterogeneousMasked_headMajorantMean
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    (MajorizedCutSystem.iterNext r
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)).headMajorantMean =
      mean (linearFormsProduct
        (((s + 1) + r) + 1) N ν
        (apCSHeterogeneousOrderedStageFaceExponent
          r s active j)) := by
  rw [←
    MajorizedCutSystem.iterNextDecoded_headMajorantMean
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)]
  exact
    iterNextDecoded_apTwoCopyHeterogeneousMasked_headMajorantMean
      r s N ν active g j hrest

/-! ## Copy-aware terminal selector -/

/-- At the terminal cube, a non-distinguished face vertex is selected
exactly when its value at the distinguished coordinate chooses an active
copy for that face. -/
def apCSHeterogeneousTerminalExponent
    {k : ℕ}
    (active : Bool → Fin k → Bool)
    (j : Fin k) :
    LinearFormsExponent k :=
  fun i ω =>
    if hij : i = j then false
    else active (ω ⟨j, fun h => hij h.symm⟩) i

@[simp]
theorem apCSHeterogeneousTerminalExponent_distinguished
    {k : ℕ}
    (active : Bool → Fin k → Bool)
    (j : Fin k)
    (ω : DeletedCube k j) :
    apCSHeterogeneousTerminalExponent active j j ω =
      false := by
  simp [apCSHeterogeneousTerminalExponent]

/-- The fully doubled majorant on one non-distinguished face selects the
`false` and `true` terminal halves independently. -/
theorem terminalFaceHeterogeneousMajorantProduct_eq
    (m N : ℕ)
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin ((m + 1) + 1) → Bool)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (p : Bool → ZMod N)
    (a : Fin (m + 1) → ZMod N × ZMod N) :
    (∏ bits : Fin m → Bool,
      apTwoCopyCutTest (m + 1) N
        (apCopyMaskedFaceMajorant ν active)
        j p t
        (eraseCoordinate t
          (fun q =>
            selectPair (a q)
              (@Fin.insertNth m
                (fun _ => Bool) t false bits q)))) =
      ∏ ω :
          DeletedCube ((m + 1) + 1)
            (j.succAbove t),
        if active
            (ω ⟨j, (Fin.succAbove_ne j t).symm⟩)
            (j.succAbove t)
        then
          ν (apLinearForm ((m + 1) + 1) N
            (j.succAbove t) ω
            (apCSTerminalCubeEquiv
              (m + 1) N j (p, a)))
        else 1 := by
  classical
  simp_rw [apTwoCopyCutTest_eraseCoordinate]
  simp_rw [apCopyMaskedFaceMajorant_apply]
  let F :
      Bool → (Fin m → Bool) → ℝ :=
    fun b bits =>
      if active b (j.succAbove t) then
        ν (apSimplexForm ((m + 1) + 1) N
          (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j (p b)
              (fun q =>
                selectPair (a q)
                  (@Fin.insertNth m
                    (fun _ => Bool) t false bits q)))
            (j.succAbove t)))
      else 1
  change
    (∏ bits : Fin m → Bool,
      ∏ b : Bool, F b bits) = _
  rw [Finset.prod_comm]
  rw [← Fintype.prod_prod_type
    (fun q : Bool × (Fin m → Bool) =>
      F q.1 q.2)]
  apply Fintype.prod_equiv
    (apCSTerminalFaceVertexEquiv m j t)
  intro bits
  change
    F bits.1 bits.2 =
      if active
          (apCSTerminalFaceVertex m j t bits
            ⟨j, (Fin.succAbove_ne j t).symm⟩)
          (j.succAbove t)
      then
        ν (apLinearForm ((m + 1) + 1) N
          (j.succAbove t)
          (apCSTerminalFaceVertex m j t bits)
          (apCSTerminalCubeEquiv
            (m + 1) N j (p, a)))
      else 1
  rw [apCSTerminalFaceVertex_distinguished]
  by_cases hactive :
      active bits.1 (j.succAbove t) = true
  · simp only [hactive, if_true]
    unfold F
    simp only [hactive, if_true]
    apply congrArg ν
    exact
      apSimplexForm_eq_apLinearForm_terminalFaceVertex
        m N j t p a bits.1 bits.2
  · have hfalse :
        active bits.1 (j.succAbove t) = false := by
      exact Bool.eq_false_of_not_eq_true hactive
    simp [F, hfalse]

namespace MajorizedCutSystem

/-- The terminal core is unchanged by the choice of designated masks and
is the centered distinguished-face product. -/
theorem terminalCoreProduct_apTwoCopyHeterogeneousMasked
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (p : Bool → ZMod N)
    (a : Fin n → ZMod N × ZMod N) :
    terminalCoreProduct
        (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
          n N ν active g j hrest) p a =
      faceCenteredProduct (n + 1) N ν j
        (apCSTerminalCubeEquiv n N j (p, a)) := by
  classical
  unfold terminalCoreProduct
  unfold apTwoCopyHeterogeneousMaskedMajorizedCutSystem
  change
    (∏ bits : Fin n → Bool,
      apFaceCenteredCore n N ν j
        (fun i => selectPair (a i) (bits i))) =
      faceCenteredProduct (n + 1) N ν j
        (Fin.insertNth j p
          (fun i => selectPair (a i)))
  rw [faceCenteredProduct_insertNth]
  unfold apFaceCenteredCore
  apply Fintype.prod_congr
  intro bits
  rw [apSimplexForm_finTupleToDeletedVector]

/-- Every heterogeneous designated majorant contributes precisely the
copy-aware terminal selector. -/
theorem terminalMajorantProduct_apTwoCopyHeterogeneousMasked
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (p : Bool → ZMod N)
    (a : Fin n → ZMod N × ZMod N) :
    terminalMajorantProduct
        (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
          n N ν active g j hrest) p a =
      linearFormsProduct (n + 1) N ν
        (apCSHeterogeneousTerminalExponent active j)
        (apCSTerminalCubeEquiv n N j (p, a)) := by
  classical
  cases n with
  | zero =>
      rw [terminalMajorantProduct_zero]
      unfold linearFormsProduct
      apply Eq.symm
      apply Fintype.prod_eq_one
      intro i
      have hi : i = j := by
        apply Fin.ext
        omega
      subst i
      apply Fintype.prod_eq_one
      intro ω
      simp
  | succ m =>
      rw [terminalMajorantProduct_succ]
      change
        (∏ t : Fin (m + 1),
          ∏ bits : Fin m → Bool,
            apTwoCopyCutTest (m + 1) N
              (apCopyMaskedFaceMajorant ν active)
              j p t
              (eraseCoordinate t
                (fun q =>
                  selectPair (a q)
                    (@Fin.insertNth m
                      (fun _ => Bool) t false
                        bits q)))) = _
      rw [linearFormsProduct,
        Fin.prod_univ_succAbove _ j]
      have hself :
          (∏ ω : DeletedCube ((m + 1) + 1) j,
            if
              apCSHeterogeneousTerminalExponent
                active j j ω
            then
              ν (apLinearForm ((m + 1) + 1)
                N j ω
                (apCSTerminalCubeEquiv
                  (m + 1) N j (p, a)))
            else 1) = 1 := by
        apply Fintype.prod_eq_one
        intro ω
        simp
      rw [hself, one_mul]
      apply Fintype.prod_congr
      intro t
      rw [terminalFaceHeterogeneousMajorantProduct_eq]
      apply Fintype.prod_congr
      intro ω
      simp [apCSHeterogeneousTerminalExponent,
        Fin.succAbove_ne]

/-- Pointwise terminal identity for the decoded heterogeneous system. -/
theorem iterNextTerminalDecoded_apTwoCopyHeterogeneousMasked_core
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (p : Bool → ZMod N)
    (a : Fin n → ZMod N × ZMod N) :
    (iterNextTerminalDecoded
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        n N ν active g j hrest)).core
        (p, a) (fun i => Fin.elim0 i) =
      faceCenteredProduct (n + 1) N ν j
          (apCSTerminalCubeEquiv n N j (p, a)) *
        linearFormsProduct (n + 1) N ν
          (apCSHeterogeneousTerminalExponent active j)
          (apCSTerminalCubeEquiv
            n N j (p, a)) := by
  rw [iterNextTerminalDecoded_core]
  rw [
    terminalCoreProduct_apTwoCopyHeterogeneousMasked,
    terminalMajorantProduct_apTwoCopyHeterogeneousMasked]
  ring

/-- The fully iterated heterogeneous system has the centered distinguished
face times exactly the copy-aware terminal CFZ selector. -/
theorem iterNextTerminal_apTwoCopyHeterogeneousMasked_form_of_fintype
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (stageFintype :
      Fintype
        (CSStageParam
          (Bool → ZMod N) (ZMod N) n)) :
    @form
        (CSStageParam
          (Bool → ZMod N) (ZMod N) n)
        (ZMod N) 0 stageFintype
        (inferInstance : Fintype (ZMod N))
        (iterNextTerminal n
          (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
            n N ν active g j hrest)) =
      mean (fun x =>
        faceCenteredProduct (n + 1) N ν j x *
          linearFormsProduct (n + 1) N ν
            (apCSHeterogeneousTerminalExponent
              active j) x) := by
  letI : Fintype
      (CSStageParam
        (Bool → ZMod N) (ZMod N) n) :=
    stageFintype
  rw [← reindex_form
    (iterNextTerminal n
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        n N ν active g j hrest))
    (csStageParamEquiv
      (Bool → ZMod N) (ZMod N) n).symm]
  unfold form mean₂
  simp only [Finset.univ_eq_empty,
    Finset.prod_empty, mul_one]
  apply mean_equiv
    (apCSTerminalCubeEquiv n N j)
  intro p
  change
    mean (fun x : Fin 0 → ZMod N =>
      (iterNextTerminalDecoded
        (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
          n N ν active g j hrest)).core p x) = _
  rw [show
    (fun x : Fin 0 → ZMod N =>
      (iterNextTerminalDecoded
        (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
          n N ν active g j hrest)).core p x) =
      fun _ =>
        (iterNextTerminalDecoded
          (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
            n N ν active g j hrest)).core
          p (fun i => Fin.elim0 i) by
      funext x
      apply congrArg
      funext i
      exact Fin.elim0 i]
  rw [mean_const]
  exact
    iterNextTerminalDecoded_apTwoCopyHeterogeneousMasked_core
      n N ν active g j hrest p.1 p.2

/-- Convenience specialization using the canonical stage finite instance. -/
theorem iterNextTerminal_apTwoCopyHeterogeneousMasked_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    (iterNextTerminal n
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        n N ν active g j hrest)).form =
      mean (fun x =>
        faceCenteredProduct (n + 1) N ν j x *
          linearFormsProduct (n + 1) N ν
            (apCSHeterogeneousTerminalExponent
              active j) x) :=
  iterNextTerminal_apTwoCopyHeterogeneousMasked_form_of_fintype
    n N ν active g j hrest inferInstance

/-- Exact copy-aware terminal certificate. -/
theorem apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZTerminal
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    HasCFZTerminal ν j
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        n N ν active g j hrest) := by
  apply hasCFZTerminal_of_iterNextTerminal_form
    j
    (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
      n N ν active g j hrest)
    (apCSHeterogeneousTerminalExponent active j)
  · exact
      apCSHeterogeneousTerminalExponent_distinguished
        active j
  · intro stageFintype
    exact
      iterNextTerminal_apTwoCopyHeterogeneousMasked_form_of_fintype
        n N ν active g j hrest stageFintype

/-- Every copy-aware paid stage moment, together with the terminal
identity, assembles into a structural certificate at an arbitrary point of
the native `iterNext` tower. -/
theorem apTwoCopyHeterogeneousMasked_iterNext_hasCFZCertificate
    (k r s N : ℕ) [NeZero N]
    (hk : k = s + r)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (k + 1) → Bool)
    (g : Bool → APFaceWeightFamily k N)
    (j : Fin (k + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    HasCFZCertificate ν j
      (iterNext r
        (castArity hk
          (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
            k N ν active g j hrest))) := by
  induction s generalizing k r with
  | zero =>
      subst k
      have hterminal :=
        apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZTerminal
          (0 + r) N ν active g j hrest
      have hstage :=
        hterminal.iterNext j r 0
          (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
            (0 + r) N ν active g j hrest)
      change
        HasCFZTerminal ν j
          (iterNext r
            (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
              (0 + r) N ν active g j hrest))
      exact hstage
  | succ s ih =>
      subst k
      let S :=
        apTwoCopyHeterogeneousMaskedMajorizedCutSystem
          ((s + 1) + r) N ν active g j hrest
      change
        HasCFZCertificate ν j
          (iterNext r S)
      refine
        ⟨apCSHeterogeneousOrderedStageFaceExponent
            r s active j,
          ?_, ?_⟩
      · exact
          iterNext_apTwoCopyHeterogeneousMasked_headMajorantMean
            r s N ν active g j hrest
      · have hk' :
            (s + 1) + r = s + (r + 1) := by
          omega
        have htail :
            HasCFZCertificate ν j
              (iterNext (r + 1)
                (castArity hk' S)) :=
          ih ((s + 1) + r) (r + 1) hk'
            active g j hrest
        have hrelRaw :=
          iterNext_next_eq_iterNext_succ_reindex
            s r (castArity hk' S)
        have hround :
            castArity
                (show s + (r + 1) =
                    (s + 1) + r by omega)
                (castArity hk' S) =
              S := by
          simpa only [] using
            castArity_symm hk' S
        have hrel :
            (iterNext r S).next =
              (iterNext (r + 1)
                (castArity hk' S)).reindex
                  (csStageAppendPairEquiv
                    (Bool → ZMod N) (ZMod N) r) := by
          rw [hround] at hrelRaw
          exact hrelRaw
        rw [hrel]
        exact htail.reindex j
          (iterNext (r + 1)
            (castArity hk' S))
          (csStageAppendPairEquiv
            (Bool → ZMod N) (ZMod N) r)

/-- Full structural CFZ certificate for independent masks on the two
copies. -/
theorem apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZCertificate
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    HasCFZCertificate ν j
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        n N ν active g j hrest) := by
  have hstage :=
    apTwoCopyHeterogeneousMasked_iterNext_hasCFZCertificate
      n 0 n N (by omega)
      ν active g j hrest
  have hreindexed :=
    hstage.reindex j
      (iterNext 0
        (castArity (show n = n + 0 by omega)
          (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
            n N ν active g j hrest)))
      (csStageZeroEquiv
        (Bool → ZMod N) (ZMod N)).symm
  change
    HasCFZCertificate ν j
      ((apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        n N ν active g j hrest).reindex
          (Equiv.refl (Bool → ZMod N))) at hreindexed
  rw [reindex_refl] at hreindexed
  exact hreindexed

end MajorizedCutSystem

/-! ## Quantitative correlation bounds -/

/-- Quantitative CFZ root bound for independent masks on the two projected
copies. -/
theorem HasLinearFormsCondition.abs_apTwoCopyCenteredCorrelation_le_of_heterogeneousMasked
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (active : Bool → Fin (m + 2) → Bool)
    (g : Bool → APFaceWeightFamily (m + 1) N)
    (j : Fin (m + 2))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |apTwoCopyCenteredCorrelation
        (m + 1) N ν g j| ≤ ε := by
  rw [←
    apTwoCopyHeterogeneousMaskedMajorizedCutSystem_form
      (m + 1) N ν active g j hrest]
  exact
    MajorizedCutSystem.abs_form_le_of_hasCFZCertificate
      hLF j
      (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        (m + 1) N ν active g j hrest)
      (MajorizedCutSystem.apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZCertificate
        (m + 1) N ν active g j hrest)
      hε hconvert

/-- Mask with the `false` copy sparse and the `true` copy already bounded
by one. -/
def apFalseSparseTrueDenseMask
    {k : ℕ} (active : Fin k → Bool) :
    Bool → Fin k → Bool :=
  fun b i => if b then false else active i

@[simp]
theorem apFalseSparseTrueDenseMask_false
    {k : ℕ} (active : Fin k → Bool)
    (i : Fin k) :
    apFalseSparseTrueDenseMask active false i =
      active i := by
  rfl

@[simp]
theorem apFalseSparseTrueDenseMask_true
    {k : ℕ} (active : Fin k → Bool)
    (i : Fin k) :
    apFalseSparseTrueDenseMask active true i =
      false := by
  rfl

/-- Cross-copy specialization: the `false` copy is dominated facewise by
the active `ν` mask and the `true` copy is bounded by one. -/
theorem HasLinearFormsCondition.abs_apTwoCopyCenteredCorrelation_le_of_falseSparse_trueDense
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (active : Fin (m + 2) → Bool)
    (g : Bool → APFaceWeightFamily (m + 1) N)
    (j : Fin (m + 2))
    (hSparse :
      APUntouchedFaceBounds (g false)
        (apMaskedFaceMajorant ν active) j)
    (hDense :
      ∀ t z,
        0 ≤ g true (j.succAbove t) z ∧
          g true (j.succAbove t) z ≤ 1)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |apTwoCopyCenteredCorrelation
        (m + 1) N ν g j| ≤ ε := by
  apply
    hLF.abs_apTwoCopyCenteredCorrelation_le_of_heterogeneousMasked
      (apFalseSparseTrueDenseMask active) g j
      (hrest := ?_) hε hconvert
  intro b
  cases b with
  | false =>
      change
        APUntouchedFaceBounds (g false)
          (apMaskedFaceMajorant ν active) j
      exact hSparse
  | true =>
      intro t z
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using hDense t z

/-- Mask with the `true` copy sparse and the `false` copy bounded by one. -/
def apFalseDenseTrueSparseMask
    {k : ℕ} (active : Fin k → Bool) :
    Bool → Fin k → Bool :=
  fun b i => if b then active i else false

@[simp]
theorem apFalseDenseTrueSparseMask_false
    {k : ℕ} (active : Fin k → Bool)
    (i : Fin k) :
    apFalseDenseTrueSparseMask active false i =
      false := by
  rfl

@[simp]
theorem apFalseDenseTrueSparseMask_true
    {k : ℕ} (active : Fin k → Bool)
    (i : Fin k) :
    apFalseDenseTrueSparseMask active true i =
      active i := by
  rfl

/-- Reverse cross-copy orientation: the `false` copy is bounded by one and
the `true` copy is dominated by the active `ν` mask. -/
theorem HasLinearFormsCondition.abs_apTwoCopyCenteredCorrelation_le_of_falseDense_trueSparse
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (active : Fin (m + 2) → Bool)
    (g : Bool → APFaceWeightFamily (m + 1) N)
    (j : Fin (m + 2))
    (hDense :
      ∀ t z,
        0 ≤ g false (j.succAbove t) z ∧
          g false (j.succAbove t) z ≤ 1)
    (hSparse :
      APUntouchedFaceBounds (g true)
        (apMaskedFaceMajorant ν active) j)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |apTwoCopyCenteredCorrelation
        (m + 1) N ν g j| ≤ ε := by
  apply
    hLF.abs_apTwoCopyCenteredCorrelation_le_of_heterogeneousMasked
      (apFalseDenseTrueSparseMask active) g j
      (hrest := ?_) hε hconvert
  intro b
  cases b with
  | false =>
      intro t z
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using hDense t z
  | true =>
      change
        APUntouchedFaceBounds (g true)
          (apMaskedFaceMajorant ν active) j
      exact hSparse

/-! ## Arbitrary weighted-simplex factors -/

namespace MajorizedCutSystem

/-- Structural certificates depend on the core and designated majorants,
not on the particular dominated nonnegative factors. -/
theorem HasCFZCertificate.of_core_and_majorant_eq
    {G : Type u} [Fintype G]
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      {S T : MajorizedCutSystem P G n},
      (∀ p x, S.core p x = T.core p x) →
      (∀ p i x, S.majorant p i x =
        T.majorant p i x) →
      HasCFZCertificate ν j T →
      HasCFZCertificate ν j S := by
  intro P instP n
  induction n generalizing P with
  | zero =>
      intro S T hcore _hmajorant hT
      rcases hT with ⟨other, hother, hform⟩
      refine ⟨other, hother, ?_⟩
      rw [show S.form = T.form by
        unfold form
        apply congrArg mean
        funext p
        apply congrArg mean
        funext x
        simpa using hcore p x]
      exact hform
  | succ n ih =>
      intro S T hcore hmajorant hT
      rcases hT with ⟨e, hmoment, hnext⟩
      refine ⟨e, ?_, ?_⟩
      · rw [show S.headMajorantMean =
          T.headMajorantMean by
          unfold headMajorantMean mean₂
          apply congrArg mean
          funext p
          apply congrArg mean
          funext x
          exact hmajorant p 0 x]
        exact hmoment
      · apply ih
          (S := S.next) (T := T.next)
          (fun q x => ?_)
          (fun q i x => ?_)
          hnext
        · rw [next_core_apply, next_core_apply]
          rw [hmajorant, hcore, hcore]
        · cases n with
          | zero => exact Fin.elim0 i
          | succ n =>
              change
                S.majorant q.1 i.succ
                      (Fin.cons q.2.1 x) *
                    S.majorant q.1 i.succ
                      (Fin.cons q.2.2 x) =
                  T.majorant q.1 i.succ
                      (Fin.cons q.2.1 x) *
                    T.majorant q.1 i.succ
                      (Fin.cons q.2.2 x)
              rw [hmajorant, hmajorant]

end MajorizedCutSystem

/-- Reconstruct the two-copy cut factor of an arbitrary pair of weighted
simplex systems.  The name is intentionally leaf-specific so this module
can be imported by `RelativeCountingInduction` without a declaration
cycle. -/
def heterogeneousMaskSimplexTwoCopyCutTest
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N) :
    CutTestFamily (ZMod N) n := by
  cases n with
  | zero =>
      exact fun t => Fin.elim0 t
  | succ m =>
      exact fun t z =>
        ∏ b : Bool,
          (H b).edgeWeight (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (a b)
                (Fin.insertNth t 0 z))
              (j.succAbove t))

theorem heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (y : Fin n → ZMod N) :
    heterogeneousMaskSimplexTwoCopyCutTest
        n N H j a t (eraseCoordinate t y) =
      ∏ b : Bool,
        (H b).edgeWeight (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j (a b) y)
            (j.succAbove t)) := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      unfold heterogeneousMaskSimplexTwoCopyCutTest
      apply Fintype.prod_congr
      intro b
      rw [insertNth_insertNth_eraseCoordinate]
      rw [deleteCoordinate_update_same]

theorem prod_heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → ZMod N) :
    (∏ t : Fin n,
        heterogeneousMaskSimplexTwoCopyCutTest
          n N H j a t (eraseCoordinate t y)) =
      ∏ b : Bool,
        generalSimplexIncidentProduct (H b) j (a b) y := by
  simp_rw [
    heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate]
  unfold generalSimplexIncidentProduct
  rw [Finset.prod_comm]

theorem heterogeneousMaskSimplexTwoCopyCutTest_mono
    (n N : ℕ)
    (H K : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hHK :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (K b).edgeWeight (j.succAbove t) x)
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    0 ≤ heterogeneousMaskSimplexTwoCopyCutTest
        n N H j a t z ∧
      heterogeneousMaskSimplexTwoCopyCutTest
          n N H j a t z ≤
        heterogeneousMaskSimplexTwoCopyCutTest
          n N K j a t z := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      constructor
      · unfold heterogeneousMaskSimplexTwoCopyCutTest
        exact Finset.prod_nonneg fun b _ =>
          (hHK b t _).1
      · unfold heterogeneousMaskSimplexTwoCopyCutTest
        exact Finset.prod_le_prod
          (fun b _ => (hHK b t _).1)
          (fun b _ => (hHK b t _).2)

theorem heterogeneousMaskSimplexTwoCopyCutTest_apHeterogeneous
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    heterogeneousMaskSimplexTwoCopyCutTest n N
        (fun b => apHeterogeneousSimplexSystem n N (g b))
        j a t z =
      apTwoCopyCutTest n N g j a t z := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => rfl

/-- Centered two-copy correlation for arbitrary weighted-simplex factors. -/
noncomputable def heterogeneousMaskSimplexTwoCopyCenteredCorrelation
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1)) : ℝ :=
  mean₂ fun a : Bool → ZMod N =>
    fun y : Fin n → ZMod N =>
      apFaceCenteredCore n N ν j y *
        ∏ b : Bool,
          generalSimplexIncidentProduct
            (H b) j (a b) y

/-- Arbitrary factors below the two copy-dependent AP majorants. -/
noncomputable def heterogeneousMaskSimplexMajorizedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apCopyMaskedFaceMajorant ν active b)).edgeWeight
                (j.succAbove t) x) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a =>
    heterogeneousMaskSimplexTwoCopyCutTest n N H j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (apCopyMaskedFaceMajorant ν active) j a
  factor_nonneg := by
    intro a t z
    have hmono :=
      heterogeneousMaskSimplexTwoCopyCutTest_mono
        n N H
        (fun b =>
          apHeterogeneousSimplexSystem n N
            (apCopyMaskedFaceMajorant ν active b))
        j hrest a t z
    exact hmono.1
  factor_le_majorant := by
    intro a t z
    have hmono :=
      heterogeneousMaskSimplexTwoCopyCutTest_mono
        n N H
        (fun b =>
          apHeterogeneousSimplexSystem n N
            (apCopyMaskedFaceMajorant ν active b))
        j hrest a t z
    rw [←
      heterogeneousMaskSimplexTwoCopyCutTest_apHeterogeneous
        n N (apCopyMaskedFaceMajorant ν active)
        j a t z]
    exact hmono.2

theorem heterogeneousMaskSimplexMajorizedCutSystem_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apCopyMaskedFaceMajorant ν active b)).edgeWeight
                (j.succAbove t) x) :
    (heterogeneousMaskSimplexMajorizedCutSystem
        n N ν active H j hrest).form =
      heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        n N ν H j := by
  unfold MajorizedCutSystem.form
  unfold heterogeneousMaskSimplexMajorizedCutSystem
  unfold heterogeneousMaskSimplexTwoCopyCenteredCorrelation
  apply congrArg mean
  funext a
  apply congrArg mean
  funext y
  change
    apFaceCenteredCore n N ν j y *
        ∏ t : Fin n,
          heterogeneousMaskSimplexTwoCopyCutTest
            n N H j a t (eraseCoordinate t y) =
      apFaceCenteredCore n N ν j y *
        ∏ b : Bool,
          generalSimplexIncidentProduct
            (H b) j (a b) y
  rw [
    prod_heterogeneousMaskSimplexTwoCopyCutTest_eraseCoordinate]

namespace MajorizedCutSystem

/-- The copy-dependent AP certificate is insensitive to replacing its AP
pullback factors by arbitrary nonnegative weighted-simplex factors below
the same designated majorants. -/
theorem heterogeneousMaskSimplexMajorizedCutSystem_hasCFZCertificate
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Bool → Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apCopyMaskedFaceMajorant ν active b)).edgeWeight
                (j.succAbove t) x) :
    HasCFZCertificate ν j
      (heterogeneousMaskSimplexMajorizedCutSystem
        n N ν active H j hrest) := by
  have hmajorant :
      ∀ b,
        APUntouchedFaceBounds
          (apCopyMaskedFaceMajorant ν active b)
          (apCopyMaskedFaceMajorant ν active b) j := by
    intro b t z
    constructor
    · unfold apCopyMaskedFaceMajorant
      unfold apMaskedFaceMajorant
      split
      · exact hν z
      · exact zero_le_one
    · exact le_rfl
  let T :=
    apTwoCopyHeterogeneousMaskedMajorizedCutSystem
      n N ν active
        (apCopyMaskedFaceMajorant ν active) j hmajorant
  apply HasCFZCertificate.of_core_and_majorant_eq
    j
    (S := heterogeneousMaskSimplexMajorizedCutSystem
      n N ν active H j hrest)
    (T := T)
  · intro a y
    rfl
  · intro a t z
    rfl
  · exact
      apTwoCopyHeterogeneousMaskedMajorizedCutSystem_hasCFZCertificate
        n N ν active
          (apCopyMaskedFaceMajorant ν active) j hmajorant

end MajorizedCutSystem

/-! ## Arbitrary-factor quantitative bridge -/

/-- Quantitative CFZ root bound for arbitrary weighted-simplex factors
under independent masks on the two Boolean copies. -/
theorem HasLinearFormsCondition.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Bool → Fin (m + 2) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apCopyMaskedFaceMajorant ν active b)).edgeWeight
                (j.succAbove t) x)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν H j| ≤ ε := by
  rw [← heterogeneousMaskSimplexMajorizedCutSystem_form
    (m + 1) N ν active H j hrest]
  exact
    MajorizedCutSystem.abs_form_le_of_hasCFZCertificate
      hLF j
      (heterogeneousMaskSimplexMajorizedCutSystem
        (m + 1) N ν active H j hrest)
      (MajorizedCutSystem.heterogeneousMaskSimplexMajorizedCutSystem_hasCFZCertificate
        (m + 1) N ν hν active H j hrest)
      hε hconvert

/-- A Boolean pair of arbitrary simplex systems, with the first system in
the `false` copy and the second system in the `true` copy. -/
def heterogeneousMaskSimplexCopyPair
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => G)
  | false => H
  | true => K

@[simp]
theorem heterogeneousMaskSimplexCopyPair_false
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    heterogeneousMaskSimplexCopyPair H K false = H := by
  rfl

@[simp]
theorem heterogeneousMaskSimplexCopyPair_true
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    heterogeneousMaskSimplexCopyPair H K true = K := by
  rfl

/-- One orientation of the mixed-copy estimate: the `false` copy is below
the active AP mask, and the `true` copy lies in the unit interval. -/
theorem HasLinearFormsCondition.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseSparse_trueDense
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hH :
      ∀ i x,
        0 ≤ H.edgeWeight i x ∧
          H.edgeWeight i x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apMaskedFaceMajorant ν active)).edgeWeight i x)
    (hK : EdgeWeightsInUnitInterval K)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν
          (heterogeneousMaskSimplexCopyPair H K) j| ≤ ε := by
  apply
    hLF.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le
      hν (apFalseSparseTrueDenseMask active)
      (heterogeneousMaskSimplexCopyPair H K) j
      (hrest := ?_) hε hconvert
  intro b t x
  cases b with
  | false =>
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using
          hH (j.succAbove t) x
  | true =>
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using
          hK (j.succAbove t) x

/-- The reverse mixed-copy orientation: the `false` copy lies in the unit
interval, and the `true` copy is below the active AP mask. -/
theorem HasLinearFormsCondition.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseDense_trueSparse
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hH : EdgeWeightsInUnitInterval H)
    (hK :
      ∀ i x,
        0 ≤ K.edgeWeight i x ∧
          K.edgeWeight i x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apMaskedFaceMajorant ν active)).edgeWeight i x)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν
          (heterogeneousMaskSimplexCopyPair H K) j| ≤ ε := by
  apply
    hLF.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le
      hν (apFalseDenseTrueSparseMask active)
      (heterogeneousMaskSimplexCopyPair H K) j
      (hrest := ?_) hε hconvert
  intro b t x
  cases b with
  | false =>
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using
          hH (j.succAbove t) x
  | true =>
      simpa [apCopyMaskedFaceMajorant,
        apMaskedFaceMajorant] using
          hK (j.succAbove t) x

/-- Both orientations of the sparse--dense cross correlation follow from
one heterogeneous CFZ certificate, with the Boolean masks swapped in the
second orientation. -/
theorem HasLinearFormsCondition.abs_heterogeneousMaskSimplexCrossCorrelations_le
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hH :
      ∀ i x,
        0 ≤ H.edgeWeight i x ∧
          H.edgeWeight i x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apMaskedFaceMajorant ν active)).edgeWeight i x)
    (hK : EdgeWeightsInUnitInterval K)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν
          (heterogeneousMaskSimplexCopyPair H K) j| ≤ ε ∧
      |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν
          (heterogeneousMaskSimplexCopyPair K H) j| ≤ ε := by
  constructor
  · exact
      hLF.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseSparse_trueDense
        hν active H K j hH hK hε hconvert
  · exact
      hLF.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseDense_trueSparse
        hν active K H j hK hH hε hconvert

end Wikipedia.SzemeredisTheorem
