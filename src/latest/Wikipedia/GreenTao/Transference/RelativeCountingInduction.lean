import Wikipedia.GreenTao.Transference.RelativeCountingHeterogeneousMask

/-!
# Active-majorant recurrence for relative simplex counting

The weighted Cauchy--Schwarz decoder supplies a certificate when both
copies of every active incident face use the same AP majorant.  Relative
counting also produces two cross terms: one omitted-coordinate copy is
sparse and the other is bounded by one.  This file separates those two
issues exactly.

First, the completed homogeneous certificate is transported from AP
pullback factors to arbitrary weighted-simplex edge factors.  This is
possible because a `HasCFZCertificate` depends on the core and designated
majorants, but not on the particular nonnegative factors below them.

The second part packages the active-cardinality bookkeeping and the
one-step counting recurrence.  Its only extra strong-linear-forms input is
the pair of genuinely mixed-copy centered correlations.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Factor-independence of structural CFZ certificates -/

namespace MajorizedCutSystem

/-- A structural CFZ certificate is unchanged when the cut factors are
changed while the core and every designated majorant are kept pointwise
fixed.

This is stronger than an equality transport between structures: the two
systems may carry unrelated proofs of nonnegativity and domination. -/
theorem HasCFZCertificate.of_core_majorant_eq
    {G : Type u} [Fintype G]
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      {S T : MajorizedCutSystem P G n},
      (∀ p x, S.core p x = T.core p x) →
      (∀ p i x, S.majorant p i x = T.majorant p i x) →
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

/-! ## Arbitrary simplex factors under homogeneous AP majorants -/

/-- Reconstruct the `t`-th two-copy cut factor from arbitrary weighted
simplex systems.  The inserted zero is irrelevant because the edge of
colour `j.succAbove t` omits exactly that coordinate. -/
def simplexTwoCopyCutTest
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

/-- Evaluation on an erased shared tuple recovers the two actual incident
edge factors. -/
theorem simplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (y : Fin n → ZMod N) :
    simplexTwoCopyCutTest n N H j a t
        (eraseCoordinate t y) =
      ∏ b : Bool,
        (H b).edgeWeight (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j (a b) y)
            (j.succAbove t)) := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      unfold simplexTwoCopyCutTest
      apply Fintype.prod_congr
      intro b
      rw [insertNth_insertNth_eraseCoordinate]
      rw [deleteCoordinate_update_same]

/-- Products of the reconstructed factors are the two incident simplex
products. -/
theorem prod_simplexTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → ZMod N) :
    (∏ t : Fin n,
        simplexTwoCopyCutTest n N H j a t
          (eraseCoordinate t y)) =
      ∏ b : Bool,
        generalSimplexIncidentProduct (H b) j (a b) y := by
  simp_rw [simplexTwoCopyCutTest_eraseCoordinate]
  unfold generalSimplexIncidentProduct
  rw [Finset.prod_comm]

/-- Pointwise domination of arbitrary simplex edges gives domination of
their reconstructed two-copy cut factors. -/
theorem simplexTwoCopyCutTest_mono
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
    0 ≤ simplexTwoCopyCutTest n N H j a t z ∧
      simplexTwoCopyCutTest n N H j a t z ≤
        simplexTwoCopyCutTest n N K j a t z := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      constructor
      · unfold simplexTwoCopyCutTest
        exact Finset.prod_nonneg fun b _ => (hHK b t _).1
      · unfold simplexTwoCopyCutTest
        exact Finset.prod_le_prod
          (fun b _ => (hHK b t _).1)
          (fun b _ => (hHK b t _).2)

/-- The generic reconstructed cut factor specializes to the existing AP
pullback factor. -/
theorem simplexTwoCopyCutTest_apHeterogeneous
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    simplexTwoCopyCutTest n N
        (fun b => apHeterogeneousSimplexSystem n N (g b))
        j a t z =
      apTwoCopyCutTest n N g j a t z := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => rfl

/-- Centered two-copy projected correlation for arbitrary weighted
simplex systems. -/
noncomputable def simplexTwoCopyCenteredCorrelation
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1)) : ℝ :=
  mean₂ fun a : Bool → ZMod N => fun y : Fin n → ZMod N =>
    apFaceCenteredCore n N ν j y *
      ∏ b : Bool,
        generalSimplexIncidentProduct (H b) j (a b) y

/-- The arbitrary-factor system used for a common active mask. -/
noncomputable def simplexTwoCopyMaskedMajorizedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apMaskedFaceMajorant ν active)).edgeWeight
                (j.succAbove t) x) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a => simplexTwoCopyCutTest n N H j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (fun _ => apMaskedFaceMajorant ν active) j a
  factor_nonneg := by
    intro a t z
    have hmono :=
      simplexTwoCopyCutTest_mono n N H
        (fun _ =>
          apHeterogeneousSimplexSystem n N
            (apMaskedFaceMajorant ν active))
        j hrest a t z
    exact hmono.1
  factor_le_majorant := by
    intro a t z
    have hmono :=
      simplexTwoCopyCutTest_mono n N H
        (fun _ =>
          apHeterogeneousSimplexSystem n N
            (apMaskedFaceMajorant ν active))
        j hrest a t z
    change
      simplexTwoCopyCutTest n N H j a t z ≤
        apTwoCopyCutTest n N
          (fun _ => apMaskedFaceMajorant ν active) j a t z
    rw [← simplexTwoCopyCutTest_apHeterogeneous
      n N (fun _ => apMaskedFaceMajorant ν active)
      j a t z]
    exact hmono.2

/-- The arbitrary-factor system represents its centered projected
correlation exactly. -/
theorem simplexTwoCopyMaskedMajorizedCutSystem_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apMaskedFaceMajorant ν active)).edgeWeight
                (j.succAbove t) x) :
    (simplexTwoCopyMaskedMajorizedCutSystem
        n N ν active H j hrest).form =
      simplexTwoCopyCenteredCorrelation n N ν H j := by
  unfold MajorizedCutSystem.form
  unfold simplexTwoCopyMaskedMajorizedCutSystem
  unfold simplexTwoCopyCenteredCorrelation
  apply congrArg mean
  funext a
  apply congrArg mean
  funext y
  change
    apFaceCenteredCore n N ν j y *
        ∏ t : Fin n,
          simplexTwoCopyCutTest n N H j a t
            (eraseCoordinate t y) =
      apFaceCenteredCore n N ν j y *
        ∏ b : Bool,
          generalSimplexIncidentProduct (H b) j (a b) y
  rw [prod_simplexTwoCopyCutTest_eraseCoordinate]

/-- The arbitrary-factor system has the same core and designated
majorants as the already certified AP-pullback system. -/
theorem simplexTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apMaskedFaceMajorant ν active)).edgeWeight
                (j.succAbove t) x) :
    MajorizedCutSystem.HasCFZCertificate ν j
      (simplexTwoCopyMaskedMajorizedCutSystem
        n N ν active H j hrest) := by
  let g : Bool → APFaceWeightFamily n N :=
    fun _ => apMaskedFaceMajorant ν active
  have hg :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j := by
    intro b t z
    exact
      ⟨by
        cases hactive : active (j.succAbove t) <;>
          simp [g, hactive, hν],
        le_rfl⟩
  let T :=
    apTwoCopyMaskedMajorizedCutSystem
      n N ν active g j hg
  apply MajorizedCutSystem.HasCFZCertificate.of_core_majorant_eq
      j (S :=
        simplexTwoCopyMaskedMajorizedCutSystem
          n N ν active H j hrest) (T := T)
  · intro a y
    rfl
  · intro a t z
    rfl
  · exact
      MajorizedCutSystem.apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
        n N ν active g j hg

/-- Quantitative homogeneous-mask strong-linear-forms bound for arbitrary
weighted-simplex edge factors. -/
theorem HasLinearFormsCondition.abs_simplexTwoCopyCenteredCorrelation_le_of_masked
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apMaskedFaceMajorant ν active)).edgeWeight
                (j.succAbove t) x)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν H j| ≤ ε := by
  rw [← simplexTwoCopyMaskedMajorizedCutSystem_form
    (m + 1) N ν active H j hrest]
  exact
    MajorizedCutSystem.abs_form_le_of_hasCFZCertificate
      hLF j
      (simplexTwoCopyMaskedMajorizedCutSystem
        (m + 1) N ν active H j hrest)
      (simplexTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
        (m + 1) N ν hν active H j hrest)
      hε hconvert

/-! ## Active-face cardinality and the comparison invariant -/

/-- The finite set of faces whose designated majorant is still `ν`. -/
def activeFaceSet
    {k : ℕ} (active : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => active i = true

/-- Number of still-sparse face majorants. -/
def activeFaceCount
    {k : ℕ} (active : Fin k → Bool) : ℕ :=
  (activeFaceSet active).card

@[simp]
theorem mem_activeFaceSet
    {k : ℕ} (active : Fin k → Bool) (i : Fin k) :
    i ∈ activeFaceSet active ↔ active i = true := by
  simp [activeFaceSet]

/-- Deactivation erases exactly the selected active face. -/
theorem activeFaceSet_deactivateFace
    {k : ℕ} (active : Fin k → Bool) (j : Fin k) :
    activeFaceSet (deactivateFace active j) =
      (activeFaceSet active).erase j := by
  ext i
  by_cases hij : i = j
  · subst i
    simp [deactivateFace]
  · simp [deactivateFace, hij]

/-- Deactivating an active face lowers the active count by one. -/
theorem activeFaceCount_deactivateFace
    {k : ℕ} (active : Fin k → Bool) (j : Fin k)
    (hj : active j = true) :
    activeFaceCount (deactivateFace active j) + 1 =
      activeFaceCount active := by
  unfold activeFaceCount
  rw [activeFaceSet_deactivateFace]
  exact Finset.card_erase_add_one
    (mem_activeFaceSet active j |>.2 hj)

/-- A mask has no active faces exactly when all of its entries are false. -/
theorem activeFaceCount_eq_zero_iff
    {k : ℕ} (active : Fin k → Bool) :
    activeFaceCount active = 0 ↔
      ∀ i, active i = false := by
  constructor
  · intro h i
    have hcard : (activeFaceSet active).card = 0 := h
    have hempty : activeFaceSet active = ∅ :=
      Finset.card_eq_zero.mp hcard
    have hi : i ∉ activeFaceSet active := by
      rw [hempty]
      simp
    have hne : active i ≠ true := by
      simpa using hi
    cases hactive : active i
    · rfl
    · exact (hne hactive).elim
  · intro h
    unfold activeFaceCount activeFaceSet
    simp [h]

/-- Pointwise nonnegative domination of every edge of one simplex system
by the corresponding edge of another. -/
def SimplexEdgeMajorizedBy
    {G : Type*} {n : ℕ}
    (H M : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) : Prop :=
  ∀ i x,
    0 ≤ H.edgeWeight i x ∧
      H.edgeWeight i x ≤ M.edgeWeight i x

/-- The AP simplex system carrying the Boolean-mask majorants. -/
def apMaskedSimplexMajorantSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N) :=
  apHeterogeneousSimplexSystem n N
    (apMaskedFaceMajorant ν active)

/-- Relative counting for arbitrary simplex edge functions under the
canonical AP mask.

Allowing arbitrary edge functions is essential: inserting a lower-face cut
into one edge is how the induction proves projected face-cut discrepancy. -/
def MaskedSimplexComparisonLe
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (cutError countError : ℝ) : Prop :=
  ∀ (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)),
    SimplexEdgeMajorizedBy H
      (apMaskedSimplexMajorantSystem n N ν active) →
    EdgeWeightsInUnitInterval K →
    EdgeFaceCutDiscrepancyLe H K cutError →
    |H.simplexCount - K.simplexCount| ≤ countError

/-- Empty active mask: both systems are fully bounded, so the established
bounded face-cut comparison is the induction base. -/
theorem maskedSimplexComparisonLe_of_inactive
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (hactive : ∀ i, active i = false)
    (cutError : ℝ) :
    MaskedSimplexComparisonLe n N ν active
      cutError (((n + 1 : ℕ) : ℝ) * cutError) := by
  intro H K hH hK hcut
  have hHunit : EdgeWeightsInUnitInterval H := by
    intro i x
    refine ⟨(hH i x).1, ?_⟩
    have hupper := (hH i x).2
    change
      H.edgeWeight i x ≤
        apMaskedFaceMajorant ν active i
          (apSimplexForm (n + 1) N i x) at hupper
    rw [apMaskedFaceMajorant_of_inactive
      ν active i _ (hactive i)] at hupper
    exact hupper
  exact simplexCount_abs_sub_le_of_edgeFaceCutDiscrepancy
    H K hHunit hK hcut

/-- Cardinality-zero form of the bounded induction base. -/
theorem maskedSimplexComparisonLe_of_activeFaceCount_zero
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (hactive : activeFaceCount active = 0)
    (cutError : ℝ) :
    MaskedSimplexComparisonLe n N ν active
      cutError (((n + 1 : ℕ) : ℝ) * cutError) :=
  maskedSimplexComparisonLe_of_inactive
    n N ν active
    ((activeFaceCount_eq_zero_iff active).1 hactive)
    cutError

/-! ## Replacing one canonical edge by a whole-face function -/

/-- Replace the selected edge by an arbitrary function in canonical
`Fin n` face coordinates. -/
noncomputable def setSimplexEdge
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G) where
  edgeWeight i x :=
    if hij : i = j then
      f (deletedFaceTuple j (hij ▸ x))
    else H.edgeWeight i x

@[simp]
theorem setSimplexEdge_selected
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) j) :
    (setSimplexEdge H j f).edgeWeight j x =
      f (deletedFaceTuple j x) := by
  simp [setSimplexEdge]

theorem setSimplexEdge_other
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j i : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (hij : i ≠ j)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) i) :
    (setSimplexEdge H j f).edgeWeight i x =
      H.edgeWeight i x := by
  simp [setSimplexEdge, hij]

@[simp]
theorem canonicalEdgeFunction_setSimplexEdge_selected
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    canonicalEdgeFunction (setSimplexEdge H j f) j = f := by
  funext y
  simp [canonicalEdgeFunction]

theorem canonicalEdgeFunction_setSimplexEdge_other
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j i : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (hij : i ≠ j) :
    canonicalEdgeFunction (setSimplexEdge H j f) i =
      canonicalEdgeFunction H i := by
  funext y
  simp [canonicalEdgeFunction,
    setSimplexEdge_other H j i f hij]

@[simp]
theorem generalSimplexIncidentProduct_setSimplexEdge
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct
        (setSimplexEdge H j f) j a y =
      generalSimplexIncidentProduct H j a y := by
  unfold generalSimplexIncidentProduct
  apply Fintype.prod_congr
  intro t
  exact setSimplexEdge_other H j
    (j.succAbove t) f (Fin.succAbove_ne j t) _

@[simp]
theorem generalSimplexProjectedWeight_setSimplexEdge
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    generalSimplexProjectedWeight
        (setSimplexEdge H j f) j =
      generalSimplexProjectedWeight H j := by
  funext y
  unfold generalSimplexProjectedWeight
  apply congrArg mean
  funext a
  exact generalSimplexIncidentProduct_setSimplexEdge
    H j f a y

@[simp]
theorem generalSimplexDistinguishedWeight_setSimplexEdge
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    generalSimplexDistinguishedWeight
        (setSimplexEdge H j f) j = f := by
  funext y
  simp [generalSimplexDistinguishedWeight]

/-- Replacing one edge turns the simplex count into the projected weight
paired with the replacement. -/
theorem setSimplexEdge_simplexCount
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    (setSimplexEdge H j f).simplexCount =
      mean (fun y =>
        generalSimplexProjectedWeight H j y * f y) := by
  rw [generalSimplexCount_eq_projectedPairing,
    generalSimplexProjectedWeight_setSimplexEdge,
    generalSimplexDistinguishedWeight_setSimplexEdge]

/-- A unit-bounded replacement at `j` deactivates that face while
preserving all other masked majorizations. -/
theorem setSimplexEdge_majorized_deactivateFace
    {n N : ℕ}
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)}
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem n N ν active))
    (j : Fin (n + 1))
    {f : (Fin n → ZMod N) → ℝ}
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    SimplexEdgeMajorizedBy
      (setSimplexEdge H j f)
      (apMaskedSimplexMajorantSystem n N ν
        (deactivateFace active j)) := by
  intro i x
  by_cases hij : i = j
  · subst i
    rw [setSimplexEdge_selected]
    change
      0 ≤ f (deletedFaceTuple j x) ∧
        f (deletedFaceTuple j x) ≤
          apMaskedFaceMajorant ν
            (deactivateFace active j) j
            (apSimplexForm (n + 1) N j x)
    rw [apMaskedFaceMajorant_of_inactive
      ν (deactivateFace active j) j _
      (deactivateFace_selected active j)]
    exact hf _
  · rw [setSimplexEdge_other H j i f hij]
    have hi := hH i x
    change
      0 ≤ H.edgeWeight i x ∧
        H.edgeWeight i x ≤
          apMaskedFaceMajorant ν active i
            (apSimplexForm (n + 1) N i x) at hi
    change
      0 ≤ H.edgeWeight i x ∧
        H.edgeWeight i x ≤
          apMaskedFaceMajorant ν
            (deactivateFace active j) i
            (apSimplexForm (n + 1) N i x)
    simpa [apMaskedFaceMajorant, deactivateFace, hij] using hi

/-- Replacing one edge of a bounded system by another unit-bounded
function preserves boundedness. -/
theorem setSimplexEdge_unitInterval
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1))
    {f : (Fin n → G) → ℝ}
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    EdgeWeightsInUnitInterval (setSimplexEdge H j f) := by
  intro i x
  by_cases hij : i = j
  · subst i
    simpa using hf (deletedFaceTuple j x)
  · simpa [setSimplexEdge_other H j i f hij] using hH i x

/-- Replacing the same edge on both sides preserves edgewise face-cut
discrepancy. -/
theorem EdgeFaceCutDiscrepancyLe.setSimplexEdge_same
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε)
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    EdgeFaceCutDiscrepancyLe
      (setSimplexEdge H j f)
      (setSimplexEdge K j f) ε := by
  intro i
  by_cases hij : i = j
  · subst i
    rw [canonicalEdgeFunction_setSimplexEdge_selected,
      canonicalEdgeFunction_setSimplexEdge_selected]
    exact
      (FaceCutDiscrepancyLe.refl f).mono
        (hcut j).epsilon_nonneg
  · rw [canonicalEdgeFunction_setSimplexEdge_other
      H j i f hij,
      canonicalEdgeFunction_setSimplexEdge_other
      K j i f hij]
    exact hcut i

/-- One application of the lower-active-count comparison after replacing
the selected face by a common bounded whole-face function. -/
theorem MaskedSimplexComparisonLe.setSimplexEdge_same
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {cutError countError : ℝ}
    (j : Fin (n + 1))
    (hlower :
      MaskedSimplexComparisonLe n N ν
        (deactivateFace active j) cutError countError)
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)}
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem n N ν active))
    (hK : EdgeWeightsInUnitInterval K)
    (hcut : EdgeFaceCutDiscrepancyLe H K cutError)
    {f : (Fin n → ZMod N) → ℝ}
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    |(setSimplexEdge H j f).simplexCount -
        (setSimplexEdge K j f).simplexCount| ≤
      countError :=
  hlower
    (setSimplexEdge H j f)
    (setSimplexEdge K j f)
    (setSimplexEdge_majorized_deactivateFace hH j hf)
    (setSimplexEdge_unitInterval hK j hf)
    (hcut.setSimplexEdge_same j f)

/-! ## The exact mixed-copy strong-linear-forms interface -/

/-- A Boolean pair of simplex systems, with `H` in the false copy and `K`
in the true copy. -/
def simplexCopyPair
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => G)
  | false => H
  | true => K

/-- Mean of a product over independent finite coordinates. -/
theorem mean_prod_separable
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → ℝ) (g : Y → ℝ) :
    mean (fun p : X × Y => f p.1 * g p.2) =
      mean f * mean g := by
  calc
    mean (fun p : X × Y => f p.1 * g p.2) =
        mean₂ (fun x => fun y => f x * g y) :=
      mean_prod_type (fun x : X => fun y : Y => f x * g y)
    _ = mean (fun x => mean (fun y => f x * g y)) := by
      rfl
    _ =
        mean (fun x => f x * mean g) := by
      apply congrArg mean
      funext x
      exact mean_smul (f x) g
    _ = mean (fun x => mean g * f x) := by
      apply congrArg mean
      funext x
      ring
    _ = mean g * mean f := mean_smul _ _
    _ = mean f * mean g := mul_comm _ _

/-- A general two-copy correlation is the centered face paired with the
product of the two conditional projections. -/
theorem simplexTwoCopyCenteredCorrelation_eq_projected
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1)) :
    simplexTwoCopyCenteredCorrelation n N ν H j =
      mean (fun y =>
        apFaceCenteredCore n N ν j y *
          generalSimplexProjectedWeight (H false) j y *
          generalSimplexProjectedWeight (H true) j y) := by
  unfold simplexTwoCopyCenteredCorrelation
  rw [mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext y
  calc
    mean (fun a : Bool → ZMod N =>
        apFaceCenteredCore n N ν j y *
          ∏ b : Bool,
            generalSimplexIncidentProduct (H b) j (a b) y) =
        mean (fun p : ZMod N × ZMod N =>
          apFaceCenteredCore n N ν j y *
            (generalSimplexIncidentProduct
              (H false) j p.1 y *
             generalSimplexIncidentProduct
              (H true) j p.2 y)) := by
      apply mean_equiv (boolEndpointEquiv (ZMod N))
      intro a
      simp only [Fintype.prod_bool]
      change
        apFaceCenteredCore n N ν j y *
            (generalSimplexIncidentProduct
                (H true) j (a true) y *
              generalSimplexIncidentProduct
                (H false) j (a false) y) =
          apFaceCenteredCore n N ν j y *
            (generalSimplexIncidentProduct
                (H false) j (a false) y *
              generalSimplexIncidentProduct
                (H true) j (a true) y)
      ring
    _ =
        apFaceCenteredCore n N ν j y *
          mean (fun p : ZMod N × ZMod N =>
            generalSimplexIncidentProduct
              (H false) j p.1 y *
            generalSimplexIncidentProduct
              (H true) j p.2 y) := by
      exact mean_smul _ _
    _ =
        apFaceCenteredCore n N ν j y *
          (mean (fun a : ZMod N =>
              generalSimplexIncidentProduct
                (H false) j a y) *
           mean (fun a : ZMod N =>
              generalSimplexIncidentProduct
                (H true) j a y)) := by
      apply congrArg
        (fun z => apFaceCenteredCore n N ν j y * z)
      exact mean_prod_separable
        (fun a : ZMod N =>
          generalSimplexIncidentProduct (H false) j a y)
        (fun a : ZMod N =>
          generalSimplexIncidentProduct (H true) j a y)
    _ =
        apFaceCenteredCore n N ν j y *
          generalSimplexProjectedWeight (H false) j y *
          generalSimplexProjectedWeight (H true) j y := by
      unfold generalSimplexProjectedWeight
      ring

/-- The two genuinely mixed-copy centered correlations required by one
active-majorant recurrence step.

The homogeneous `H,H` and `K,K` correlations are already consequences of
the terminal decoder.  Only these two orientations require independent
majorant masks on the two initial Boolean copies. -/
def HasSparseDenseCrossCorrelationLe
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (ε : ℝ) : Prop :=
  |simplexTwoCopyCenteredCorrelation n N ν
      (simplexCopyPair H K) j| ≤ ε ∧
  |simplexTwoCopyCenteredCorrelation n N ν
      (simplexCopyPair K H) j| ≤ ε

/-- Mask-level form of the only heterogeneous strong-linear-forms input
needed by an induction step.

It quantifies over the arbitrary sparse and dense simplex systems appearing
in `MaskedSimplexComparisonLe`.  A copy-dependent CFZ certificate can
discharge this interface directly: the false and true Boolean copies use
the active AP mask and the constant-one mask, respectively, and the second
conjunct swaps those two masks. -/
def HasActiveFaceCrossCorrelationLe
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (ε : ℝ) : Prop :=
  ∀ (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)),
    SimplexEdgeMajorizedBy H
      (apMaskedSimplexMajorantSystem n N ν active) →
    EdgeWeightsInUnitInterval K →
    HasSparseDenseCrossCorrelationLe n N ν H K j ε

/-- The heterogeneous-mask decoder discharges the exact cross-correlation
interface needed by the active-face recurrence. -/
theorem HasLinearFormsCondition.hasActiveFaceCrossCorrelationLe
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (j : Fin (m + 2))
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    HasActiveFaceCrossCorrelationLe
      (m + 1) N ν active j ε := by
  intro H K hH hK
  have hcross :=
    hLF.abs_heterogeneousMaskSimplexCrossCorrelations_le
      hν active H K j
      (by
        simpa [SimplexEdgeMajorizedBy,
          apMaskedSimplexMajorantSystem] using hH)
      hK hε hconvert
  simpa [HasSparseDenseCrossCorrelationLe,
    simplexTwoCopyCenteredCorrelation,
    heterogeneousMaskSimplexTwoCopyCenteredCorrelation,
    simplexCopyPair,
    heterogeneousMaskSimplexCopyPair] using hcross

/-- Homogeneous sparse-copy correlation, specialized from the arbitrary
factor terminal decoder. -/
theorem HasLinearFormsCondition.abs_simplexTwoCopyCenteredCorrelation_le_of_majorized
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem
          (m + 1) N ν active))
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => H) j| ≤ ε := by
  exact
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_masked
      hν active (fun _ => H) j
      (fun _b t x => hH (j.succAbove t) x)
      hε hconvert

/-- Homogeneous dense-copy correlation.  The common decoder mask is empty,
so every designated incident majorant is one. -/
theorem HasLinearFormsCondition.abs_simplexTwoCopyCenteredCorrelation_le_of_unit
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hK : EdgeWeightsInUnitInterval K)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => K) j| ≤ ε := by
  apply
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_masked
      hν (fun _ => false) (fun _ => K) j
      _ hε hconvert
  intro _b t x
  refine ⟨(hK (j.succAbove t) x).1, ?_⟩
  simpa [apMaskedFaceMajorant] using
    (hK (j.succAbove t) x).2

/-- The same empty-mask correlation with all incident factors one bounds
the mean of the centered distinguished AP face. -/
theorem HasLinearFormsCondition.abs_mean_apFaceCenteredCore_le
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (m + 2))
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |mean (apFaceCenteredCore (m + 1) N ν j)| ≤ ε := by
  have h :=
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_unit
      hν
      (oneWeightedSimplexSystem (ZMod N) (m + 1))
      j
      (fun _ _ => ⟨zero_le_one, le_rfl⟩)
      hε hconvert
  rw [simplexTwoCopyCenteredCorrelation_eq_projected] at h
  simpa using h

/-- Four homogeneous/mixed correlation estimates control the centered
second moment of the difference of the two projected weights. -/
theorem abs_centered_projectedDifference_sq_le
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    {ε : ℝ}
    (hHH :
      |simplexTwoCopyCenteredCorrelation n N ν
        (fun _ => H) j| ≤ ε)
    (hKK :
      |simplexTwoCopyCenteredCorrelation n N ν
        (fun _ => K) j| ≤ ε)
    (hcross :
      HasSparseDenseCrossCorrelationLe
        n N ν H K j ε) :
    |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          (generalSimplexProjectedWeight H j y -
            generalSimplexProjectedWeight K j y) ^ 2)| ≤
      4 * ε := by
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  have hHH' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          A y * A y)| ≤ ε := by
    rw [← simplexTwoCopyCenteredCorrelation_eq_projected
      n N ν (fun _ => H) j]
    exact hHH
  have hHK' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          A y * B y)| ≤ ε := by
    have h := hcross.1
    rw [simplexTwoCopyCenteredCorrelation_eq_projected] at h
    simpa [A, B, simplexCopyPair] using h
  have hKH' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          B y * A y)| ≤ ε := by
    have h := hcross.2
    rw [simplexTwoCopyCenteredCorrelation_eq_projected] at h
    simpa [A, B, simplexCopyPair] using h
  have hKK' :
      |mean (fun y =>
        apFaceCenteredCore n N ν j y *
          B y * B y)| ≤ ε := by
    rw [← simplexTwoCopyCenteredCorrelation_eq_projected
      n N ν (fun _ => K) j]
    exact hKK
  have hexpand :
      mean (fun y =>
        apFaceCenteredCore n N ν j y *
          (A y - B y) ^ 2) =
        mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * A y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * B y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * A y) +
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * B y) := by
    rw [← mean_sub, ← mean_sub, ← mean_add]
    apply congrArg mean
    funext y
    ring
  rw [hexpand]
  calc
    |mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * A y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * B y) -
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * A y) +
        mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * B y)| ≤
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * A y)| +
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * A y * B y)| +
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * A y)| +
        |mean (fun y =>
          apFaceCenteredCore n N ν j y * B y * B y)| := by
      calc
        |(mean (fun y =>
              apFaceCenteredCore n N ν j y * A y * A y) -
            mean (fun y =>
              apFaceCenteredCore n N ν j y * A y * B y) -
            mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * A y)) +
            mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| ≤
            |mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * A y) -
              mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * B y) -
              mean (fun y =>
                apFaceCenteredCore n N ν j y * B y * A y)| +
            |mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| :=
          abs_add_le _ _
        _ ≤
            (|mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * A y) -
              mean (fun y =>
                apFaceCenteredCore n N ν j y * A y * B y)| +
             |mean (fun y =>
                apFaceCenteredCore n N ν j y * B y * A y)|) +
            |mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| := by
          gcongr
          exact abs_sub _ _
        _ ≤
            ((|mean (fun y =>
                  apFaceCenteredCore n N ν j y * A y * A y)| +
               |mean (fun y =>
                  apFaceCenteredCore n N ν j y * A y * B y)|) +
             |mean (fun y =>
                apFaceCenteredCore n N ν j y * B y * A y)|) +
            |mean (fun y =>
              apFaceCenteredCore n N ν j y * B y * B y)| := by
          gcongr
          exact abs_sub _ _
    _ ≤ ε + ε + ε + ε :=
      add_le_add
        (add_le_add (add_le_add hHH' hHK') hKH') hKK'
    _ = 4 * ε := by ring

/-! ## Direct cut term and projected pointwise bounds -/

/-- The incident product of one fixed simplex system, reconstructed as a
cut-test family after fixing the omitted vertex. -/
def simplexIncidentCutTest
    {G : Type*} {n : ℕ}
    (K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G) :
    CutTestFamily G n :=
  fun t z =>
    K.edgeWeight (j.succAbove t)
      (deleteCoordinate
        (Fin.insertNth j a
          (insertErasedCoordinate t a z))
        (j.succAbove t))

@[simp]
theorem simplexIncidentCutTest_eraseCoordinate
    {G : Type*} [DecidableEq G] {n : ℕ}
    (K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (t : Fin n) (y : Fin n → G) :
    simplexIncidentCutTest K j a t
        (eraseCoordinate t y) =
      K.edgeWeight (j.succAbove t)
        (deleteCoordinate (Fin.insertNth j a y)
          (j.succAbove t)) := by
  rw [simplexIncidentCutTest,
    insertErasedCoordinate_eraseCoordinate,
    Fin.insertNth_update]
  exact deleteCoordinate_update_same _ _ _
    |> congrArg (K.edgeWeight (j.succAbove t))

/-- A bounded simplex gives a bounded reconstructed incident cut. -/
theorem simplexIncidentCutTest_bounded
    {G : Type*} {n : ℕ}
    {K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) (a : G) :
    IsBoundedCutTest (simplexIncidentCutTest K j a) := by
  constructor
  · intro t z
    exact (hK (j.succAbove t) _).1
  · intro t z
    exact (hK (j.succAbove t) _).2

/-- The reconstructed cut product is exactly the incident simplex
product. -/
theorem cutTestProduct_simplexIncidentCutTest
    {G : Type*} [DecidableEq G] {n : ℕ}
    (K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (y : Fin n → G) :
    cutTestProduct (simplexIncidentCutTest K j a) y =
      generalSimplexIncidentProduct K j a y := by
  unfold cutTestProduct generalSimplexIncidentProduct
  apply Fintype.prod_congr
  intro t
  exact simplexIncidentCutTest_eraseCoordinate
    K j a t y

/-- Edgewise face-cut discrepancy controls the term in which the
distinguished edge is changed while every incident factor comes from the
bounded system. -/
theorem abs_directProjectedDifference_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) :
    |mean (fun y =>
        (generalSimplexDistinguishedWeight H j y -
          generalSimplexDistinguishedWeight K j y) *
        generalSimplexProjectedWeight K j y)| ≤ ε := by
  have hrewrite :
      mean (fun y =>
          (generalSimplexDistinguishedWeight H j y -
            generalSimplexDistinguishedWeight K j y) *
          generalSimplexProjectedWeight K j y) =
        mean (fun a : G =>
          faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j)
            (simplexIncidentCutTest K j a)) := by
    unfold generalSimplexProjectedWeight
    calc
      mean (fun y =>
          (generalSimplexDistinguishedWeight H j y -
            generalSimplexDistinguishedWeight K j y) *
            mean (fun a =>
              generalSimplexIncidentProduct K j a y)) =
          mean (fun y =>
            mean (fun a =>
              (generalSimplexDistinguishedWeight H j y -
                generalSimplexDistinguishedWeight K j y) *
              generalSimplexIncidentProduct K j a y)) := by
        apply congrArg mean
        funext y
        exact
          (mean_smul
            (generalSimplexDistinguishedWeight H j y -
              generalSimplexDistinguishedWeight K j y)
            (fun a =>
              generalSimplexIncidentProduct K j a y)).symm
      _ = mean₂ (fun y => fun a =>
            (generalSimplexDistinguishedWeight H j y -
              generalSimplexDistinguishedWeight K j y) *
            generalSimplexIncidentProduct K j a y) := by
        rfl
      _ = mean₂ (fun a => fun y =>
            (generalSimplexDistinguishedWeight H j y -
              generalSimplexDistinguishedWeight K j y) *
            generalSimplexIncidentProduct K j a y) :=
        mean₂_comm _
      _ = mean (fun a : G =>
          faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j)
            (simplexIncidentCutTest K j a)) := by
        unfold mean₂
        apply congrArg mean
        funext a
        unfold faceCutDifferenceCorrelation
        apply congrArg mean
        funext y
        rw [cutTestProduct_simplexIncidentCutTest]
        rfl
  rw [hrewrite]
  calc
    |mean (fun a : G =>
        faceCutDifferenceCorrelation
          (canonicalEdgeFunction H j)
          (canonicalEdgeFunction K j)
          (simplexIncidentCutTest K j a))| ≤
        mean (fun a : G =>
          |faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j)
            (simplexIncidentCutTest K j a)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : G => ε) := by
      apply mean_mono
      intro a
      exact hcut j
        (simplexIncidentCutTest K j a)
        (simplexIncidentCutTest_bounded hK j a)
    _ = ε := mean_const _

/-- Full edge majorization supplies the untouched-edge form used by the
generic projection API. -/
theorem SimplexEdgeMajorizedBy.generalSimplexUntouchedBounds
    {G : Type*} {n : ℕ}
    {H M : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (h : SimplexEdgeMajorizedBy H M)
    (j : Fin (n + 1)) :
    GeneralSimplexUntouchedBounds H M j :=
  fun t x => h (j.succAbove t) x

/-- A projected weight of a fully bounded simplex lies in `[0,1]`. -/
theorem generalSimplexProjectedWeight_mem_unitInterval
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1))
    (y : Fin n → G) :
    0 ≤ generalSimplexProjectedWeight K j y ∧
      generalSimplexProjectedWeight K j y ≤ 1 := by
  have hrest := hK.generalSimplexUntouchedBounds_one j
  constructor
  · exact generalSimplexProjectedWeight_nonneg hrest y
  · calc
      generalSimplexProjectedWeight K j y ≤
          generalSimplexProjectedWeight
            (oneWeightedSimplexSystem G n) j y :=
        generalSimplexProjectedWeight_mono hrest y
      _ = 1 := by
        rw [generalSimplexProjectedWeight_one]

/-! ## Truncation and the lower-cardinality quadratic term -/

/-- The part of the projected square lost by truncating its sparse
projection is controlled solely by the first two moments of the projected
majorant. -/
theorem HasProjectedMajorantMoments.abs_mean_projectedDifference_mul_excess_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {M A B : Ω → ℝ} {η : ℝ}
    (hM : HasProjectedMajorantMoments M η)
    (hA0 : ∀ x, 0 ≤ A x)
    (hAM : ∀ x, A x ≤ M x)
    (hB0 : ∀ x, 0 ≤ B x)
    (hB1 : ∀ x, B x ≤ 1) :
    |mean (fun x =>
        (A x - B x) *
          (A x - truncateAtOne A x))| ≤
      3 * η + 2 * Real.sqrt (3 * η) := by
  have hpoint :
      ∀ x,
        |(A x - B x) *
            (A x - truncateAtOne A x)| ≤
          (M x + 1) * |M x - 1| := by
    intro x
    rw [abs_mul]
    have hleft : |A x - B x| ≤ M x + 1 := by
      calc
        |A x - B x| ≤ |A x| + |B x| := abs_sub _ _
        _ = A x + B x := by
          rw [abs_of_nonneg (hA0 x),
            abs_of_nonneg (hB0 x)]
        _ ≤ M x + 1 := add_le_add (hAM x) (hB1 x)
    have hright :
        |A x - truncateAtOne A x| ≤
          |M x - 1| :=
      (abs_sub_truncateAtOne_le_excessAboveOne
        hAM x).trans
        (excessAboveOne_le_abs_sub_one M x)
    exact mul_le_mul hleft hright
      (abs_nonneg _) (by linarith [hM.nonneg x])
  have hmajorantPoint :
      ∀ x,
        (M x + 1) * |M x - 1| ≤
          (M x - 1) ^ 2 +
            2 * |M x - 1| := by
    intro x
    let d := M x - 1
    have hd :
        d * |d| ≤ d ^ 2 := by
      by_cases hd0 : 0 ≤ d
      · rw [abs_of_nonneg hd0]
        simp [pow_two]
      · have hdle : d ≤ 0 := le_of_not_ge hd0
        exact
          (mul_nonpos_of_nonpos_of_nonneg
            hdle (abs_nonneg d)).trans (sq_nonneg d)
    change
      (M x + 1) * |d| ≤ d ^ 2 + 2 * |d|
    calc
      (M x + 1) * |d| =
          d * |d| + 2 * |d| := by
        dsimp [d]
        ring
      _ ≤ d ^ 2 + 2 * |d| :=
        add_le_add hd le_rfl
  calc
    |mean (fun x =>
        (A x - B x) *
          (A x - truncateAtOne A x))| ≤
        mean (fun x =>
          |(A x - B x) *
            (A x - truncateAtOne A x)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun x =>
          (M x + 1) * |M x - 1|) :=
      mean_mono hpoint
    _ ≤ mean (fun x =>
          (M x - 1) ^ 2 +
            2 * |M x - 1|) :=
      mean_mono hmajorantPoint
    _ =
        mean (fun x => (M x - 1) ^ 2) +
          2 * mean (fun x => |M x - 1|) := by
      rw [mean_add, mean_smul]
    _ ≤ 3 * η + 2 * Real.sqrt (3 * η) :=
      add_le_add
        hM.centeredSecondMoment_le
        (mul_le_mul_of_nonneg_left
          hM.centeredAbsMean_le_sqrt (by norm_num))

/-- The lower-active-count comparison controls the quadratic pairing of
the projected difference against its bounded truncation difference. -/
theorem MaskedSimplexComparisonLe.abs_mean_projectedDifference_mul_truncatedDifference_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {cutError countError : ℝ}
    (j : Fin (n + 1))
    (hlower :
      MaskedSimplexComparisonLe n N ν
        (deactivateFace active j) cutError countError)
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)}
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem n N ν active))
    (hK : EdgeWeightsInUnitInterval K)
    (hcut : EdgeFaceCutDiscrepancyLe H K cutError) :
    |mean (fun y =>
        (generalSimplexProjectedWeight H j y -
          generalSimplexProjectedWeight K j y) *
        (truncateAtOne
            (generalSimplexProjectedWeight H j) y -
          generalSimplexProjectedWeight K j y))| ≤
      2 * countError := by
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  let C := truncateAtOne A
  have hA0 : ∀ y, 0 ≤ A y := by
    intro y
    exact generalSimplexProjectedWeight_nonneg
      (hH.generalSimplexUntouchedBounds j) y
  have hC : ∀ y, 0 ≤ C y ∧ C y ≤ 1 :=
    truncateAtOne_mem_unitInterval hA0
  have hB : ∀ y, 0 ≤ B y ∧ B y ≤ 1 :=
    generalSimplexProjectedWeight_mem_unitInterval hK j
  have hcountC :=
    MaskedSimplexComparisonLe.setSimplexEdge_same
      j hlower hH hK hcut hC
  have hcountB :=
    MaskedSimplexComparisonLe.setSimplexEdge_same
      j hlower hH hK hcut hB
  rw [setSimplexEdge_simplexCount,
    setSimplexEdge_simplexCount] at hcountC hcountB
  change
    |mean (fun y => A y * C y) -
      mean (fun y => B y * C y)| ≤ countError at hcountC
  change
    |mean (fun y => A y * B y) -
      mean (fun y => B y * B y)| ≤ countError at hcountB
  have hexpand :
      mean (fun y => (A y - B y) * (C y - B y)) =
        (mean (fun y => A y * C y) -
          mean (fun y => B y * C y)) -
        (mean (fun y => A y * B y) -
          mean (fun y => B y * B y)) := by
    rw [← mean_sub, ← mean_sub, ← mean_sub]
    apply congrArg mean
    funext y
    ring
  change
    |mean (fun y => (A y - B y) * (C y - B y))| ≤
      2 * countError
  rw [hexpand]
  calc
    |(mean (fun y => A y * C y) -
        mean (fun y => B y * C y)) -
      (mean (fun y => A y * B y) -
        mean (fun y => B y * B y))| ≤
        |mean (fun y => A y * C y) -
          mean (fun y => B y * C y)| +
        |mean (fun y => A y * B y) -
          mean (fun y => B y * B y)| :=
      abs_sub _ _
    _ ≤ countError + countError :=
      add_le_add hcountC hcountB
    _ = 2 * countError := by ring

/-- Projected moments and the lower-active-count comparison give an
ordinary `L²` bound for the difference of the sparse and dense
projections.

The first summand is the part above the truncation level one.  The second
summand is a genuine lower-mask simplex count, because the common
truncated projection can be inserted as the selected edge. -/
theorem HasProjectedMajorantMoments.mean_projectedDifference_sq_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {η cutError countError : ℝ}
    (j : Fin (n + 1))
    (hMoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight
          (apMaskedSimplexMajorantSystem n N ν active) j) η)
    (hlower :
      MaskedSimplexComparisonLe n N ν
        (deactivateFace active j) cutError countError)
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)}
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem n N ν active))
    (hK : EdgeWeightsInUnitInterval K)
    (hcut : EdgeFaceCutDiscrepancyLe H K cutError) :
    mean (fun y =>
        (generalSimplexProjectedWeight H j y -
          generalSimplexProjectedWeight K j y) ^ 2) ≤
      3 * η + 2 * Real.sqrt (3 * η) +
        2 * countError := by
  let M :=
    generalSimplexProjectedWeight
      (apMaskedSimplexMajorantSystem n N ν active) j
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  let C := truncateAtOne A
  have hrest :
      GeneralSimplexUntouchedBounds H
        (apMaskedSimplexMajorantSystem n N ν active) j :=
    hH.generalSimplexUntouchedBounds j
  have hA0 : ∀ y, 0 ≤ A y :=
    generalSimplexProjectedWeight_nonneg hrest
  have hAM : ∀ y, A y ≤ M y :=
    generalSimplexProjectedWeight_mono hrest
  have hB :
      ∀ y, 0 ≤ B y ∧ B y ≤ 1 :=
    generalSimplexProjectedWeight_mem_unitInterval hK j
  have hexcess :
      |mean (fun y =>
          (A y - B y) * (A y - C y))| ≤
        3 * η + 2 * Real.sqrt (3 * η) := by
    exact
      hMoments.abs_mean_projectedDifference_mul_excess_le
        hA0 hAM (fun y => (hB y).1) (fun y => (hB y).2)
  have htruncated :
      |mean (fun y =>
          (A y - B y) * (C y - B y))| ≤
        2 * countError := by
    exact
      hlower.abs_mean_projectedDifference_mul_truncatedDifference_le
        j hH hK hcut
  have hexpand :
      mean (fun y => (A y - B y) ^ 2) =
        mean (fun y =>
          (A y - B y) * (A y - C y)) +
        mean (fun y =>
          (A y - B y) * (C y - B y)) := by
    rw [← mean_add]
    apply congrArg mean
    funext y
    ring
  change
    mean (fun y => (A y - B y) ^ 2) ≤
      3 * η + 2 * Real.sqrt (3 * η) +
        2 * countError
  rw [hexpand]
  calc
    mean (fun y =>
          (A y - B y) * (A y - C y)) +
        mean (fun y =>
          (A y - B y) * (C y - B y)) ≤
        |mean (fun y =>
          (A y - B y) * (A y - C y))| +
        |mean (fun y =>
          (A y - B y) * (C y - B y))| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤
        (3 * η + 2 * Real.sqrt (3 * η)) +
          2 * countError :=
      add_le_add hexcess htruncated
    _ =
        3 * η + 2 * Real.sqrt (3 * η) +
          2 * countError := by ring

/-! ## One active-face recurrence -/

/-- Weighted Cauchy--Schwarz controls the projection-difference term in one
active-face replacement.

The homogeneous sparse/sparse and dense/dense correlations, as well as the
mean of the distinguished AP majorant, come from the completed common-mask
decoder.  `HasActiveFaceCrossCorrelationLe` supplies exactly the two
heterogeneous cross terms. -/
theorem HasLinearFormsCondition.abs_mean_distinguished_mul_projectedDifference_le
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    {active : Fin (m + 2) → Bool}
    {cutError countError ξ σ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (m + 2))
    (hj : active j = true)
    (hlower :
      MaskedSimplexComparisonLe (m + 1) N ν
        (deactivateFace active j) cutError countError)
    (hcross :
      HasActiveFaceCrossCorrelationLe
        (m + 1) N ν active j ξ)
    (hξ : 0 ≤ ξ)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ξ ^ (2 ^ (m + 1)))
    (hσ : 0 ≤ σ)
    (hroot :
      (1 + ξ) *
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError + 4 * ξ) ≤
        σ ^ 2)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem
          (m + 1) N ν active))
    (hK : EdgeWeightsInUnitInterval K)
    (hcut : EdgeFaceCutDiscrepancyLe H K cutError) :
    |mean (fun y =>
        generalSimplexDistinguishedWeight H j y *
          (generalSimplexProjectedWeight H j y -
            generalSimplexProjectedWeight K j y))| ≤
      σ := by
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  let u := generalSimplexDistinguishedWeight H j
  let v : (Fin (m + 1) → ZMod N) → ℝ :=
    fun y =>
      ν (apSimplexForm (m + 2) N j
        (finTupleToDeletedVector j y))
  let c := apFaceCenteredCore (m + 1) N ν j
  have hMoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight
          (apMaskedSimplexMajorantSystem
            (m + 1) N ν active) j) η := by
    change
      HasProjectedMajorantMoments
        (apMaskedProjectedMajorant
          (m + 1) N ν active j) η
    exact
      hLF.hasProjectedMajorantMoments_apMaskedProjection
        hν active j
  have hL2 :
      mean (fun y => (A y - B y) ^ 2) ≤
        3 * η + 2 * Real.sqrt (3 * η) +
          2 * countError := by
    exact
      hMoments.mean_projectedDifference_sq_le
        j hlower hH hK hcut
  have hHH :
      |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => H) j| ≤ ξ :=
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_majorized
      hν active H j hH hξ hconvert
  have hKK :
      |simplexTwoCopyCenteredCorrelation
        (m + 1) N ν (fun _ => K) j| ≤ ξ :=
    hLF.abs_simplexTwoCopyCenteredCorrelation_le_of_unit
      hν K j hK hξ hconvert
  have hcentered :
      |mean (fun y =>
          c y * (A y - B y) ^ 2)| ≤
        4 * ξ := by
    exact
      abs_centered_projectedDifference_sq_le
        (m + 1) N ν H K j hHH hKK
        (hcross H K hH hK)
  have hcore :
      |mean c| ≤ ξ :=
    hLF.abs_mean_apFaceCenteredCore_le
      hν j hξ hconvert
  have hv0 : ∀ y, 0 ≤ v y :=
    fun y => hν _
  have hu0 : ∀ y, 0 ≤ u y := by
    intro y
    exact (hH j (finTupleToDeletedVector j y)).1
  have huv : ∀ y, u y ≤ v y := by
    intro y
    have hupper :=
      (hH j (finTupleToDeletedVector j y)).2
    simpa [u, v, generalSimplexDistinguishedWeight,
      apMaskedSimplexMajorantSystem,
      apMaskedFaceMajorant, hj] using hupper
  have hvc : ∀ y, v y = c y + 1 := by
    intro y
    simp [v, c, apFaceCenteredCore]
  have hmeanV :
      mean v ≤ 1 + ξ := by
    have hrewrite :
        mean v = mean c + 1 := by
      calc
        mean v = mean (fun y => c y + 1) := by
          apply congrArg mean
          funext y
          exact hvc y
        _ = mean c + mean (fun _ => (1 : ℝ)) :=
          mean_add _ _
        _ = mean c + 1 := by rw [mean_const]
    rw [hrewrite]
    linarith [le_abs_self (mean c), hcore]
  have hweighted0 :
      0 ≤ mean (fun y =>
        v y * (A y - B y) ^ 2) :=
    mean_nonneg fun y =>
      mul_nonneg (hv0 y) (sq_nonneg _)
  have hweighted :
      mean (fun y =>
          v y * (A y - B y) ^ 2) ≤
        3 * η + 2 * Real.sqrt (3 * η) +
          2 * countError + 4 * ξ := by
    have hrewrite :
        mean (fun y =>
            v y * (A y - B y) ^ 2) =
          mean (fun y => (A y - B y) ^ 2) +
          mean (fun y =>
            c y * (A y - B y) ^ 2) := by
      rw [← mean_add]
      apply congrArg mean
      funext y
      rw [hvc y]
      ring
    rw [hrewrite]
    calc
      mean (fun y => (A y - B y) ^ 2) +
          mean (fun y =>
            c y * (A y - B y) ^ 2) ≤
          mean (fun y => (A y - B y) ^ 2) +
            |mean (fun y =>
              c y * (A y - B y) ^ 2)| :=
        add_le_add le_rfl (le_abs_self _)
      _ ≤
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError) + 4 * ξ :=
        add_le_add hL2 hcentered
      _ =
          3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError + 4 * ξ := by ring
  have hcs :
      mean (fun y => u y * (A y - B y)) ^ 2 ≤
        mean v *
          mean (fun y =>
            v y * (A y - B y) ^ 2) :=
    mean_mul_sq_le_majorized u v
      (fun y => A y - B y) hu0 huv
  have hproduct :
      mean v *
          mean (fun y =>
            v y * (A y - B y) ^ 2) ≤
        (1 + ξ) *
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError + 4 * ξ) := by
    exact
      mul_le_mul hmeanV hweighted hweighted0
        (by linarith)
  have hsquare :
      |mean (fun y => u y * (A y - B y))| ^ 2 ≤
        σ ^ 2 := by
    rw [sq_abs]
    exact hcs.trans (hproduct.trans hroot)
  exact
    (sq_le_sq₀
      (abs_nonneg
        (mean (fun y => u y * (A y - B y))))
      hσ).mp hsquare

/-- One active face can be removed from the majorant mask.

The new error is the weighted Cauchy--Schwarz root `σ`, plus one direct
face-cut error for changing the distinguished edge itself.  All dependence
on a copy-dependent decoder is confined to
`HasActiveFaceCrossCorrelationLe`. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_step
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    {active : Fin (m + 2) → Bool}
    {cutError countError ξ σ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (m + 2))
    (hj : active j = true)
    (hlower :
      MaskedSimplexComparisonLe (m + 1) N ν
        (deactivateFace active j) cutError countError)
    (hcross :
      HasActiveFaceCrossCorrelationLe
        (m + 1) N ν active j ξ)
    (hξ : 0 ≤ ξ)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ξ ^ (2 ^ (m + 1)))
    (hσ : 0 ≤ σ)
    (hroot :
      (1 + ξ) *
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * countError + 4 * ξ) ≤
        σ ^ 2) :
    MaskedSimplexComparisonLe (m + 1) N ν active
      cutError (σ + cutError) := by
  intro H K hH hK hcut
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  let u := generalSimplexDistinguishedWeight H j
  let v := generalSimplexDistinguishedWeight K j
  have hmain :
      |mean (fun y => u y * (A y - B y))| ≤ σ := by
    exact
      hLF.abs_mean_distinguished_mul_projectedDifference_le
        hν j hj hlower hcross hξ hconvert hσ hroot
        H K hH hK hcut
  have hdirect :
      |mean (fun y => (u y - v y) * B y)| ≤ cutError := by
    exact abs_directProjectedDifference_le hcut hK j
  rw [generalSimplexCount_eq_projectedPairing H j,
    generalSimplexCount_eq_projectedPairing K j]
  change
    |mean (fun y => A y * u y) -
      mean (fun y => B y * v y)| ≤
      σ + cutError
  have hexpand :
      mean (fun y => A y * u y) -
          mean (fun y => B y * v y) =
        mean (fun y => u y * (A y - B y)) +
          mean (fun y => (u y - v y) * B y) := by
    rw [← mean_add, ← mean_sub]
    apply congrArg mean
    funext y
    ring
  rw [hexpand]
  exact
    (abs_add_le _ _).trans
      (add_le_add hmain hdirect)

/-- A proved comparison remains valid after enlarging its count-error
budget. -/
theorem MaskedSimplexComparisonLe.mono_countError
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {cutError countError countError' : ℝ}
    (h :
      MaskedSimplexComparisonLe n N ν active
        cutError countError)
    (hle : countError ≤ countError') :
    MaskedSimplexComparisonLe n N ν active
      cutError countError' := by
  intro H K hH hK hcut
  exact (h H K hH hK hcut).trans hle

/-- Strong induction on the number of active faces.

`error r` is the count-error budget after `r` sparse faces remain.  The
base hypothesis absorbs the bounded telescoping estimate, while
`hroot` is exactly the numerical recurrence generated by weighted
Cauchy--Schwarz.  The only structural hypothesis not discharged in this
file is `hcross`, the copy-dependent two-orientation correlation bound. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_of_activeFaceInduction
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    {cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (error : ℕ → ℝ)
    (hbase :
      (((m + 2 : ℕ) : ℝ) * cutError) ≤ error 0)
    (hcross :
      ∀ (active : Fin (m + 2) → Bool)
        (j : Fin (m + 2)),
        active j = true →
        HasActiveFaceCrossCorrelationLe
          (m + 1) N ν active j ξ)
    (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1)))
    (hnext :
      ∀ r : ℕ, cutError ≤ error (r + 1))
    (hroot :
      ∀ r : ℕ,
        (1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * error r + 4 * ξ) ≤
          (error (r + 1) - cutError) ^ 2)
    (active : Fin (m + 2) → Bool) :
    MaskedSimplexComparisonLe (m + 1) N ν active
      cutError (error (activeFaceCount active)) := by
  classical
  let P : ℕ → Prop := fun s =>
    ∀ active : Fin (m + 2) → Bool,
      activeFaceCount active = s →
      MaskedSimplexComparisonLe (m + 1) N ν active
        cutError (error s)
  have hP : ∀ s, P s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        change
          ∀ active : Fin (m + 2) → Bool,
            activeFaceCount active = s →
            MaskedSimplexComparisonLe (m + 1) N ν active
              cutError (error s)
        intro active hcard
        by_cases hs : s = 0
        · have hzero : activeFaceCount active = 0 :=
            hcard.trans hs
          have hbaseComparison :=
            (maskedSimplexComparisonLe_of_activeFaceCount_zero
              (m + 1) N ν active hzero cutError).mono_countError
                hbase
          simpa [hs] using hbaseComparison
        · have hspos : 0 < s := Nat.pos_of_ne_zero hs
          have hsetNonempty :
              (activeFaceSet active).Nonempty := by
            exact Finset.card_pos.mp (by
              change 0 < activeFaceCount active
              rw [hcard]
              exact hspos)
          obtain ⟨j, hjset⟩ := hsetNonempty
          have hj : active j = true :=
            (mem_activeFaceSet active j).1 hjset
          let r :=
            activeFaceCount (deactivateFace active j)
          have hradd :
              r + 1 = activeFaceCount active := by
            exact activeFaceCount_deactivateFace active j hj
          have hrs : r + 1 = s := by
            rw [hradd, hcard]
          have hrlt : r < s := by omega
          have hlower :
              MaskedSimplexComparisonLe (m + 1) N ν
                (deactivateFace active j) cutError (error r) := by
            exact
              ih r hrlt (deactivateFace active j) rfl
          have hstep :
              MaskedSimplexComparisonLe (m + 1) N ν active
                cutError
                ((error (r + 1) - cutError) + cutError) := by
            exact
              hLF.maskedSimplexComparisonLe_step
                hν j hj hlower (hcross active j hj)
                hξ (hconvert j)
                (sub_nonneg.mpr (hnext r))
                (hroot r)
          have herr :
              (error (r + 1) - cutError) + cutError =
                error s := by
            rw [hrs]
            ring
          rw [← herr]
          exact hstep
  exact hP (activeFaceCount active) active rfl

/-- Fully decoded active-face induction.

The copy-dependent cross correlations are now internal consequences of the
same linear-forms condition, so callers need only provide the numerical
error schedule. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_of_linearForms
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    {cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (error : ℕ → ℝ)
    (hbase :
      (((m + 2 : ℕ) : ℝ) * cutError) ≤ error 0)
    (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1)))
    (hnext :
      ∀ r : ℕ, cutError ≤ error (r + 1))
    (hroot :
      ∀ r : ℕ,
        (1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * error r + 4 * ξ) ≤
          (error (r + 1) - cutError) ^ 2)
    (active : Fin (m + 2) → Bool) :
    MaskedSimplexComparisonLe (m + 1) N ν active
      cutError (error (activeFaceCount active)) := by
  exact
    hLF.maskedSimplexComparisonLe_of_activeFaceInduction
      hν error hbase
      (fun current j _hj =>
        hLF.hasActiveFaceCrossCorrelationLe
          hν current j hξ (hconvert j))
      hξ hconvert hnext hroot active

end Wikipedia.SzemeredisTheorem
