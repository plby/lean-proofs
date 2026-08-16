import Wikipedia.GreenTao.Transference.ProjectedFaceCutClosure
import Wikipedia.GreenTao.Transference.WeightedStrongLinearFormsCS

/-!
# CFZ certificates for projected two-copy correlations

The active-majorant induction in relative counting produces a two-copy
correlation.  The coordinate on the selected face is shared, while the
omitted simplex coordinate has two independent copies.  This file realizes
that correlation as a `MajorizedCutSystem`.

The first part supplies a reusable terminal-value theorem for systems whose
designated majorants are all one.  It identifies the fully iterated
Cauchy--Schwarz endpoint with the box moment of the original core.  Applied
to the centered AP face, the box moment is exactly `faceCenteredProduct`.

The second part defines the concrete two-copy AP cut factors and proves that
their system form is the projected correlation occurring in densification.
For factors bounded by one this gives an explicit, kernel-checked
`HasCFZCertificate`, and hence plugs the exact projected expression into the
weighted Cauchy--Schwarz API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem

/-! ## Terminal values for unit-majorant systems -/

/-- The scalar reached after all recursive `next` transformations.

This predicate deliberately forgets the intermediate factors.  At dimension
zero they have all disappeared, so only the final form remains. -/
def HasTerminalValue
    {G : Type u} [Fintype G] (value : ℝ) :
    ∀ {P : Type u} [Fintype P] {n : ℕ},
      MajorizedCutSystem P G n → Prop
  | _, _, 0, S => S.form = value
  | _, _, _n + 1, S => HasTerminalValue value S.next

/-- Changing the name of an equal terminal scalar preserves a terminal-value
certificate. -/
theorem HasTerminalValue.congr
    {G : Type u} [Fintype G]
    {P : Type u} [Fintype P] {n : ℕ}
    {S : MajorizedCutSystem P G n}
    {a b : ℝ}
    (h : HasTerminalValue a S)
    (hab : a = b) :
    HasTerminalValue b S := by
  subst b
  exact h

/-- The core field of `next`, exposed uniformly across its two
dimension-pattern branches. -/
@[simp]
theorem next_core_apply
    {P G : Type*} {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (a : G × G) (y : Fin n → G) :
    S.next.core (p, a) y =
      S.majorant p 0 y *
        S.core p (Fin.cons a.1 y) *
        S.core p (Fin.cons a.2 y) := by
  cases n <;> rfl

/-- With unit majorants, the fully iterated terminal value is the mean over
the external parameter of the box moment of the original core.

The theorem is independent of the actual cut factors.  At each `next` step
the unit head majorant disappears and the core is paired in the eliminated
coordinate, exactly matching the recursion defining `boxMoment`. -/
theorem HasUnitMajorants.hasTerminalValue_mean_boxMoment
    {G : Type u} [Fintype G] :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      (S : MajorizedCutSystem P G n),
      HasUnitMajorants S →
      HasTerminalValue
        (mean fun p : P => boxMoment n (S.core p)) S := by
  intro P instP n
  induction n generalizing P with
  | zero =>
      intro S _hunit
      change S.form =
        mean fun p : P => boxMoment 0 (S.core p)
      unfold form boxMoment mean₂
      apply congrArg mean
      funext p
      simp
  | succ n ih =>
      intro S hunit
      change
        HasTerminalValue
          (mean fun p : P =>
            boxMoment (n + 1) (S.core p))
          S.next
      have hnext :=
        ih S.next hunit.next
      apply hnext.congr
      calc
        mean (fun q : P × (G × G) =>
            boxMoment n (S.next.core q)) =
            mean₂ (fun p : P => fun a : G × G =>
              boxMoment n (S.next.core (p, a))) :=
          by
            simpa only [Prod.eta] using
              (mean_prod_type
                (fun p : P => fun a : G × G =>
                  boxMoment n (S.next.core (p, a))))
        _ = mean fun p : P =>
            boxMoment (n + 1) (S.core p) := by
          unfold mean₂
          apply congrArg mean
          funext p
          rw [boxMoment_succ]
          apply congrArg mean
          funext a
          apply congrArg (boxMoment n)
          funext y
          rw [next_core_apply]
          rw [hunit]
          simp [pairedTupleFunction]

/-- A terminal value equal to the centered distinguished-face moment is
exactly the terminal clause required by `HasCFZTerminal`.  The accompanying
selector is the empty selector on all other CFZ faces. -/
theorem HasTerminalValue.hasCFZTerminal_faceCentered
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k)
    {G : Type u} [Fintype G] :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      (S : MajorizedCutSystem P G n),
      HasTerminalValue
        (mean (faceCenteredProduct k N ν j)) S →
      HasCFZTerminal ν j S := by
  intro P instP n
  induction n generalizing P with
  | zero =>
      intro S hterminal
      refine
        ⟨emptyLinearFormsExponent k, ?_, ?_⟩
      · intro ω
        rfl
      · rw [hterminal]
        apply congrArg mean
        funext x
        rw [linearFormsProduct_empty, mul_one]
  | succ n ih =>
      intro S hterminal
      change HasCFZTerminal ν j S.next
      exact ih S.next hterminal

end MajorizedCutSystem

/-! ## The centered AP face as a box core -/

/-- The selected AP face, centered at one, in canonical `Fin n`
deleted-face coordinates. -/
noncomputable def apFaceCenteredCore
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (y : Fin n → ZMod N) : ℝ :=
  ν (apSimplexForm (n + 1) N j
      (finTupleToDeletedVector j y)) - 1

/-- The box endpoint of the centered AP core is exactly the centered
distinguished-face product in the CFZ doubled-coordinate system. -/
theorem boxMoment_apFaceCenteredCore_eq_faceCenteredProduct
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    boxMoment n (apFaceCenteredCore n N ν j) =
      mean (faceCenteredProduct (n + 1) N ν j) := by
  calc
    boxMoment n (apFaceCenteredCore n N ν j) =
        cubeMean n (apFaceCenteredCore n N ν j) :=
      boxMoment_eq_cubeMean _ _
    _ = cubeFunctionMean n
          (apFaceCenteredCore n N ν j) :=
      (cubeFunctionMean_eq_cubeMean _ _).symm
    _ = mean (faceCenteredProduct (n + 1) N ν j) := by
      rw [mean_faceCenteredProduct_eq_weightedCube]
      unfold cubeFunctionMean apFaceCenteredCore
      apply congrArg mean
      funext x
      apply Finset.prod_congr rfl
      intro ω _hω
      rw [apSimplexForm_finTupleToDeletedVector]

namespace MajorizedCutSystem

/-- A unit-majorant system whose core is the centered AP face has the
required CFZ terminal identity, independently of its cut factors. -/
theorem HasUnitMajorants.hasCFZTerminal_apFaceCenteredCore
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin (n + 1))
    {P : Type} [Fintype P] [Nonempty P]
    (S : MajorizedCutSystem P (ZMod N) n)
    (hunit : S.HasUnitMajorants)
    (hcore :
      ∀ p y, S.core p y =
        apFaceCenteredCore n N ν j y) :
    HasCFZTerminal ν j S := by
  have hterminal :
      S.HasTerminalValue
        (mean fun p : P => boxMoment n (S.core p)) :=
    hunit.hasTerminalValue_mean_boxMoment S
  have hmean :
      (mean fun p : P => boxMoment n (S.core p)) =
        mean (faceCenteredProduct (n + 1) N ν j) := by
    have hfun :
        (fun p : P => boxMoment n (S.core p)) =
          fun _p : P =>
            boxMoment n (apFaceCenteredCore n N ν j) := by
      funext p
      apply congrArg (boxMoment n)
      funext y
      exact hcore p y
    rw [hfun, mean_const]
    exact boxMoment_apFaceCenteredCore_eq_faceCenteredProduct
      n N ν j
  exact
    (hterminal.congr hmean).hasCFZTerminal_faceCentered
      j S

/-- The corresponding full CFZ certificate.  Every intermediate unit
majorant moment is the empty CFZ subproduct. -/
theorem HasUnitMajorants.hasCFZCertificate_apFaceCenteredCore
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin (n + 1))
    {P : Type} [Fintype P] [Nonempty P]
    (S : MajorizedCutSystem P (ZMod N) n)
    (hunit : S.HasUnitMajorants)
    (hcore :
      ∀ p y, S.core p y =
        apFaceCenteredCore n N ν j y) :
    HasCFZCertificate ν j S :=
  hunit.hasCFZCertificate j S
    (hunit.hasCFZTerminal_apFaceCenteredCore
      j S hcore)

end MajorizedCutSystem

/-! ## Concrete two-copy AP cut factors -/

/-- Reconstruct the `t`-th deleted-coordinate factor in the projected
two-copy correlation.

The parameter `a : Bool → ZMod N` contains the two independent copies of
the omitted coordinate `j`.  The input `z` contains every shared coordinate
except `t`; an irrelevant zero is inserted at `t`, since the corresponding
simplex face omits that coordinate. -/
def apTwoCopyCutTest
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N) :
    CutTestFamily (ZMod N) n := by
  cases n with
  | zero =>
      exact fun t => Fin.elim0 t
  | succ m =>
      exact fun t z =>
        ∏ b : Bool,
          g b (j.succAbove t)
            (apSimplexForm (m + 2) N (j.succAbove t)
              (deleteCoordinate
                (Fin.insertNth j (a b)
                  (Fin.insertNth t 0 z))
                (j.succAbove t)))

/-- Evaluating a reconstructed factor on an erased shared tuple recovers
the two actual incident AP faces. -/
theorem apTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (y : Fin n → ZMod N) :
    apTwoCopyCutTest n N g j a t
        (eraseCoordinate t y) =
      ∏ b : Bool,
        g b (j.succAbove t)
          (apSimplexForm (n + 1) N (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (a b) y)
              (j.succAbove t))) := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      unfold apTwoCopyCutTest
      apply Fintype.prod_congr
      intro b
      rw [insertNth_insertNth_eraseCoordinate]
      rw [deleteCoordinate_update_same]

/-- Products of the reconstructed cut factors are exactly the product of
the two heterogeneous incident simplex products. -/
theorem prod_apTwoCopyCutTest_eraseCoordinate
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → ZMod N) :
    (∏ t : Fin n,
        apTwoCopyCutTest n N g j a t
          (eraseCoordinate t y)) =
      ∏ b : Bool,
        apHeterogeneousIncidentProduct n N (g b) j (a b) y := by
  simp_rw [apTwoCopyCutTest_eraseCoordinate]
  unfold apHeterogeneousIncidentProduct
  rw [Finset.prod_comm]

/-- Unit-interval bounds on every incident face give a bounded two-copy cut
test. -/
theorem apTwoCopyCutTest_bounded
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hg :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤ 1)
    (a : Bool → ZMod N) :
    IsBoundedCutTest (apTwoCopyCutTest n N g j a) := by
  cases n with
  | zero =>
      constructor <;> intro t <;> exact Fin.elim0 t
  | succ m =>
      constructor
      · intro t z
        unfold apTwoCopyCutTest
        exact Finset.prod_nonneg fun b _ => (hg b t _).1
      · intro t z
        unfold apTwoCopyCutTest
        exact Finset.prod_le_one
          (fun b _ => (hg b t _).1)
          (fun b _ => (hg b t _).2)

/-- If every selected face is inactive, the reconstructed two-copy
majorant is identically one. -/
theorem apTwoCopyCutTest_masked_eq_one_of_inactive
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (hactive : ∀ i, active i = false)
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    apTwoCopyCutTest n N
        (fun _ => apMaskedFaceMajorant ν active)
        j a t z = 1 := by
  have hfamily :
      (fun _ : Bool => apMaskedFaceMajorant ν active) =
        fun _ _ _ => 1 := by
    funext b i x
    exact apMaskedFaceMajorant_of_inactive
      ν active i x (hactive i)
  rw [hfamily]
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      simp [apTwoCopyCutTest]

/-- Componentwise nonnegative domination of two face families gives
pointwise domination of their reconstructed two-copy cut tests. -/
theorem apTwoCopyCutTest_mono
    (n N : ℕ)
    (g h : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hgh :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤
            h b (j.succAbove t) z)
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    0 ≤ apTwoCopyCutTest n N g j a t z ∧
      apTwoCopyCutTest n N g j a t z ≤
        apTwoCopyCutTest n N h j a t z := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      constructor
      · unfold apTwoCopyCutTest
        exact Finset.prod_nonneg fun b _ => (hgh b t _).1
      · unfold apTwoCopyCutTest
        exact Finset.prod_le_prod
          (fun b _ => (hgh b t _).1)
          (fun b _ => (hgh b t _).2)

/-! ## A single paid active face -/

/-- Retain the activity status of one face and deactivate every other
face. -/
def isolateActiveFace
    {k : ℕ} (active : Fin k → Bool) (i : Fin k) :
    Fin k → Bool :=
  fun q => if q = i then active i else false

@[simp]
theorem isolateActiveFace_selected
    {k : ℕ} (active : Fin k → Bool) (i : Fin k) :
    isolateActiveFace active i i = active i := by
  simp [isolateActiveFace]

@[simp]
theorem isolateActiveFace_other
    {k : ℕ} (active : Fin k → Bool)
    (i q : Fin k) (hqi : q ≠ i) :
    isolateActiveFace active i q = false := by
  simp [isolateActiveFace, hqi]

/-- The incident product for a mask supported on one colour is exactly its
single masked face factor. -/
theorem apMaskedIncidentMajorantProduct_isolateActiveFace
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (t : Fin n)
    (a : ZMod N) (y : Fin n → ZMod N) :
    apMaskedIncidentMajorantProduct n N ν
        (isolateActiveFace active (j.succAbove t))
        j a y =
      apMaskedFaceMajorant ν active
        (j.succAbove t)
        (apSimplexForm (n + 1) N (j.succAbove t)
          (deleteCoordinate (Fin.insertNth j a y)
            (j.succAbove t))) := by
  unfold apMaskedIncidentMajorantProduct
  unfold apHeterogeneousIncidentProduct
  rw [Fintype.prod_eq_single t]
  · cases hactive : active (j.succAbove t) <;>
      simp [apMaskedFaceMajorant, isolateActiveFace,
        hactive]
  · intro q hqt
    have hface :
        j.succAbove q ≠ j.succAbove t := by
      intro h
      exact hqt (Fin.succAbove_right_injective h)
    rw [apMaskedFaceMajorant_of_inactive]
    exact isolateActiveFace_other active
      (j.succAbove t) (j.succAbove q) hface

/-- Pairing the two omitted-coordinate copies of the isolated incident
product gives exactly one reconstructed designated cut factor. -/
theorem prod_apMaskedIncidentMajorantProduct_isolateActiveFace
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (t : Fin n)
    (a : Bool → ZMod N)
    (y : Fin n → ZMod N) :
    (∏ b : Bool,
      apMaskedIncidentMajorantProduct n N ν
        (isolateActiveFace active (j.succAbove t))
        j (a b) y) =
      apTwoCopyCutTest n N
        (fun _ => apMaskedFaceMajorant ν active)
        j a t (eraseCoordinate t y) := by
  simp_rw [
    apMaskedIncidentMajorantProduct_isolateActiveFace]
  exact
    (apTwoCopyCutTest_eraseCoordinate n N
      (fun _ => apMaskedFaceMajorant ν active)
      j a t y).symm

/-- Boolean-indexed endpoints and an ordinary pair carry the same two
values. -/
def boolEndpointEquiv (G : Type*) :
    (Bool → G) ≃ G × G where
  toFun a := (a false, a true)
  invFun p := selectPair p
  left_inv a := by
    funext b
    cases b <;> rfl
  right_inv p :=
    Prod.ext rfl rfl

@[simp]
theorem selectPair_boolEndpointEquiv
    {G : Type*} (a : Bool → G) :
    selectPair (boolEndpointEquiv G a) = a :=
  (boolEndpointEquiv G).left_inv a

/-- The exact centered two-copy correlation produced after squaring a
projected incident average. -/
noncomputable def apTwoCopyCenteredCorrelation
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1)) : ℝ :=
  mean₂ fun a : Bool → ZMod N => fun y : Fin n → ZMod N =>
    apFaceCenteredCore n N ν j y *
      ∏ b : Bool,
        apHeterogeneousIncidentProduct n N (g b) j (a b) y

/-! ## Mixed active-majorant system -/

/-- The exact majorized system used before the active-majorant induction
has removed all sparse faces.

For an active colour, both two-copy factors are dominated by the
corresponding AP majorant `ν`; for an inactive colour they are dominated by
one. -/
noncomputable def apTwoCopyMaskedMajorizedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a => apTwoCopyCutTest n N g j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (fun _ => apMaskedFaceMajorant ν active) j a
  factor_nonneg := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (fun _ => apMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).1
  factor_le_majorant := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (fun _ => apMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).2

/-- The mixed system represents exactly the same projected two-copy
correlation; the active mask changes only the designated majorants paid by
Cauchy--Schwarz. -/
theorem apTwoCopyMaskedMajorizedCutSystem_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest).form =
      apTwoCopyCenteredCorrelation n N ν g j := by
  unfold MajorizedCutSystem.form
  unfold apTwoCopyMaskedMajorizedCutSystem
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

/-- The first majorant moment paid by the concrete mixed system is already
an ordinary CFZ subproduct.

Only the head deleted coordinate is being eliminated, so the selector is
supported on that single AP face.  The two selected vertices correspond to
the two values of the omitted coordinate `j`; all other doubled coordinates
are unused uniform fibers. -/
theorem apTwoCopyMaskedMajorizedCutSystem_headMajorantMean
    (m N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (m + 2) → Bool)
    (g : Bool → APFaceWeightFamily (m + 1) N)
    (j : Fin (m + 2))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    (apTwoCopyMaskedMajorizedCutSystem
        (m + 1) N ν active g j hrest).headMajorantMean =
      mean (linearFormsProduct (m + 2) N ν
        (apMaskedProjectedTwoCopyExponent
          (m + 1)
          (isolateActiveFace active
            (j.succAbove (0 : Fin (m + 1))))
          j)) := by
  rw [←
    mean_apMaskedProjectedMajorant_sq_eq_twoCopyLinearFormsProduct]
  change
    mean₂ (fun a : Bool → ZMod N =>
      fun z : Fin m → ZMod N =>
        apTwoCopyCutTest (m + 1) N
          (fun _ => apMaskedFaceMajorant ν active)
          j a 0 z) =
    mean (fun y : Fin (m + 1) → ZMod N =>
      mean (fun c : ZMod N =>
        apMaskedIncidentMajorantProduct
          (m + 1) N ν
          (isolateActiveFace active
            (j.succAbove (0 : Fin (m + 1))))
          j c y) ^ 2)
  calc
    mean₂ (fun a : Bool → ZMod N =>
        fun z : Fin m → ZMod N =>
          apTwoCopyCutTest (m + 1) N
            (fun _ => apMaskedFaceMajorant ν active)
            j a 0 z) =
        mean₂ (fun p : ZMod N × ZMod N =>
          fun z : Fin m → ZMod N =>
            apTwoCopyCutTest (m + 1) N
              (fun _ => apMaskedFaceMajorant ν active)
              j (selectPair p) 0 z) := by
      unfold mean₂
      apply mean_equiv (boolEndpointEquiv (ZMod N))
      intro a
      apply congrArg mean
      funext z
      exact congrArg
        (fun q =>
          apTwoCopyCutTest (m + 1) N
            (fun _ => apMaskedFaceMajorant ν active)
            j q 0 z)
        (selectPair_boolEndpointEquiv a).symm
    _ = mean₂ (fun p : ZMod N × ZMod N =>
          fun y : Fin (m + 1) → ZMod N =>
            apMaskedIncidentMajorantProduct
                (m + 1) N ν
                (isolateActiveFace active
                  (j.succAbove (0 : Fin (m + 1))))
                j p.1 y *
              apMaskedIncidentMajorantProduct
                (m + 1) N ν
                (isolateActiveFace active
                  (j.succAbove (0 : Fin (m + 1))))
                j p.2 y) := by
      unfold mean₂
      apply congrArg mean
      funext p
      rw [mean_fin_cons]
      unfold mean₂
      symm
      calc
        mean (fun d : ZMod N =>
            mean (fun z : Fin m → ZMod N =>
              apMaskedIncidentMajorantProduct
                  (m + 1) N ν
                  (isolateActiveFace active
                    (j.succAbove (0 : Fin (m + 1))))
                  j p.1 (Fin.cons d z) *
                apMaskedIncidentMajorantProduct
                  (m + 1) N ν
                  (isolateActiveFace active
                    (j.succAbove (0 : Fin (m + 1))))
                  j p.2 (Fin.cons d z))) =
            mean (fun _d : ZMod N =>
              mean (fun z : Fin m → ZMod N =>
                apTwoCopyCutTest (m + 1) N
                  (fun _ =>
                    apMaskedFaceMajorant ν active)
                  j (selectPair p) 0 z)) := by
          apply congrArg mean
          funext d
          apply congrArg mean
          funext z
          have hpoint :=
            prod_apMaskedIncidentMajorantProduct_isolateActiveFace
              (m + 1) N ν active j
              (0 : Fin (m + 1))
              (selectPair p) (Fin.cons d z)
          simpa [Fintype.prod_bool, mul_comm] using hpoint
        _ = mean (fun z : Fin m → ZMod N =>
              apTwoCopyCutTest (m + 1) N
                (fun _ => apMaskedFaceMajorant ν active)
                j (selectPair p) 0 z) :=
          mean_const _
    _ = mean₂ (fun y : Fin (m + 1) → ZMod N =>
          fun p : ZMod N × ZMod N =>
            apMaskedIncidentMajorantProduct
                (m + 1) N ν
                (isolateActiveFace active
                  (j.succAbove (0 : Fin (m + 1))))
                j p.1 y *
              apMaskedIncidentMajorantProduct
                (m + 1) N ν
                (isolateActiveFace active
                  (j.succAbove (0 : Fin (m + 1))))
                j p.2 y) :=
      mean₂_comm _
    _ = mean (fun y : Fin (m + 1) → ZMod N =>
          mean (fun c : ZMod N =>
            apMaskedIncidentMajorantProduct
              (m + 1) N ν
              (isolateActiveFace active
                (j.succAbove (0 : Fin (m + 1))))
              j c y) ^ 2) := by
      exact
        (mean_inner_sq_eq_mean₂_pair
          (fun y : Fin (m + 1) → ZMod N =>
            fun c : ZMod N =>
              apMaskedIncidentMajorantProduct
                (m + 1) N ν
                (isolateActiveFace active
                  (j.succAbove (0 : Fin (m + 1))))
                j c y)).symm

/-- Lift a certificate for the recursively transformed mixed system across
its first Cauchy--Schwarz step.

The new certificate entry is the isolated selector computed by
`apTwoCopyMaskedMajorizedCutSystem_headMajorantMean`.  Thus the remaining
work in a full mixed certificate is precisely to decode the nested
parameter carried by `next`; no analytic estimate is hidden in this
constructor. -/
theorem apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate_of_next
    (m N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (m + 2) → Bool)
    (g : Bool → APFaceWeightFamily (m + 1) N)
    (j : Fin (m + 2))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (hnext :
      MajorizedCutSystem.HasCFZCertificate ν j
        (apTwoCopyMaskedMajorizedCutSystem
          (m + 1) N ν active g j hrest).next) :
    MajorizedCutSystem.HasCFZCertificate ν j
      (apTwoCopyMaskedMajorizedCutSystem
        (m + 1) N ν active g j hrest) := by
  refine
    ⟨apMaskedProjectedTwoCopyExponent
        (m + 1)
        (isolateActiveFace active
          (j.succAbove (0 : Fin (m + 1))))
        j,
      ?_, hnext⟩
  exact
    apTwoCopyMaskedMajorizedCutSystem_headMajorantMean
      m N ν active g j hrest

/-- When the active mask is empty, the mixed system's designated
majorants are literally one. -/
theorem apTwoCopyMaskedMajorizedCutSystem_hasUnitMajorants
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (hactive : ∀ i, active i = false) :
    (apTwoCopyMaskedMajorizedCutSystem
      n N ν active g j hrest).HasUnitMajorants := by
  intro a t z
  change
    apTwoCopyCutTest n N
        (fun _ => apMaskedFaceMajorant ν active)
        j a t z = 1
  exact apTwoCopyCutTest_masked_eq_one_of_inactive
    n N ν active j hactive a t z

/-- Empty active mask: the concrete mixed system obtains a full structural
CFZ certificate without any further indexing hypothesis. -/
theorem apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate_of_inactive
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (hactive : ∀ i, active i = false) :
    MajorizedCutSystem.HasCFZCertificate ν j
      (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest) := by
  let S :=
    apTwoCopyMaskedMajorizedCutSystem
      n N ν active g j hrest
  have hunit : S.HasUnitMajorants :=
    apTwoCopyMaskedMajorizedCutSystem_hasUnitMajorants
      n N ν active g j hrest hactive
  exact hunit.hasCFZCertificate_apFaceCenteredCore
    j S (fun _ _ => rfl)

/-! ## The bounded two-copy certificate -/

/-- The concrete unit-majorant cut system representing the two-copy AP
correlation. -/
noncomputable def apTwoCopyBoundedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hg :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤ 1) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n :=
  MajorizedCutSystem.ofBoundedFactors
    (fun _ y => apFaceCenteredCore n N ν j y)
    (fun a => apTwoCopyCutTest n N g j a)
    (fun a t z =>
      (apTwoCopyCutTest_bounded n N g j hg a).nonneg t z)
    (fun a t z =>
      (apTwoCopyCutTest_bounded n N g j hg a).le_one t z)

/-- The form of the concrete system is definitionally the projected
two-copy centered correlation after regrouping the incident factors. -/
theorem apTwoCopyBoundedCutSystem_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hg :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤ 1) :
    (apTwoCopyBoundedCutSystem n N ν g j hg).form =
      apTwoCopyCenteredCorrelation n N ν g j := by
  unfold MajorizedCutSystem.form
  unfold apTwoCopyBoundedCutSystem
  unfold MajorizedCutSystem.ofBoundedFactors
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

/-- The concrete bounded two-copy system has the exact terminal CFZ
certificate required by the weighted Cauchy--Schwarz iteration. -/
theorem apTwoCopyBoundedCutSystem_hasCFZTerminal
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hg :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤ 1) :
    MajorizedCutSystem.HasCFZTerminal ν j
      (apTwoCopyBoundedCutSystem n N ν g j hg) := by
  let S := apTwoCopyBoundedCutSystem n N ν g j hg
  have hunit : S.HasUnitMajorants :=
    MajorizedCutSystem.ofBoundedFactors_hasUnitMajorants
      (fun _ y => apFaceCenteredCore n N ν j y)
      (fun a => apTwoCopyCutTest n N g j a)
      (fun a t z =>
        (apTwoCopyCutTest_bounded n N g j hg a).nonneg t z)
      (fun a t z =>
        (apTwoCopyCutTest_bounded n N g j hg a).le_one t z)
  have hterminal :
      S.HasTerminalValue
        (mean fun _a : Bool → ZMod N =>
          boxMoment n (apFaceCenteredCore n N ν j)) :=
    hunit.hasTerminalValue_mean_boxMoment S
  have hmean :
      (mean fun _a : Bool → ZMod N =>
          boxMoment n (apFaceCenteredCore n N ν j)) =
        mean (faceCenteredProduct (n + 1) N ν j) := by
    rw [mean_const]
    exact boxMoment_apFaceCenteredCore_eq_faceCenteredProduct
      n N ν j
  exact
    (hterminal.congr hmean).hasCFZTerminal_faceCentered
      j S

/-- Full structural certificate for the exact bounded two-copy projected
correlation.  Intermediate unit-majorant moments are certified by the empty
CFZ selector, while the terminal form is the centered distinguished face. -/
theorem apTwoCopyBoundedCutSystem_hasCFZCertificate
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hg :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤ 1) :
    MajorizedCutSystem.HasCFZCertificate ν j
      (apTwoCopyBoundedCutSystem n N ν g j hg) := by
  let S := apTwoCopyBoundedCutSystem n N ν g j hg
  have hunit : S.HasUnitMajorants :=
    MajorizedCutSystem.ofBoundedFactors_hasUnitMajorants
      (fun _ y => apFaceCenteredCore n N ν j y)
      (fun a => apTwoCopyCutTest n N g j a)
      (fun a t z =>
        (apTwoCopyCutTest_bounded n N g j hg a).nonneg t z)
      (fun a t z =>
        (apTwoCopyCutTest_bounded n N g j hg a).le_one t z)
  exact hunit.hasCFZCertificate j S
    (apTwoCopyBoundedCutSystem_hasCFZTerminal
      n N ν g j hg)

/-- Quantitative weighted strong-linear-forms estimate for the exact
bounded two-copy projected correlation. -/
theorem HasLinearFormsCondition.abs_apTwoCopyCenteredCorrelation_pow_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hg :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤ 1) :
    |apTwoCopyCenteredCorrelation n N ν g j| ^ (2 ^ n) ≤
      (1 + η) ^ (2 ^ n - 1) *
        ((2 : ℝ) ^ Fintype.card (DeletedCube (n + 1) j) * η) := by
  rw [← apTwoCopyBoundedCutSystem_form n N ν g j hg]
  exact
    MajorizedCutSystem.abs_form_pow_two_le_of_hasCFZCertificate
      hLF j
      (apTwoCopyBoundedCutSystem n N ν g j hg)
      (apTwoCopyBoundedCutSystem_hasCFZCertificate
        n N ν g j hg)

/-- Root-extracted weighted strong-linear-forms estimate for the exact
bounded two-copy projected correlation.

The hypothesis `hconvert` is the sole numerical conversion required by a
relative-counting application: it turns the powered Cauchy--Schwarz bound
into the desired unpowered error threshold. -/
theorem HasLinearFormsCondition.abs_apTwoCopyCenteredCorrelation_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hg :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤ 1)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ n - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (n + 1) j) * η) ≤
        ε ^ (2 ^ n)) :
    |apTwoCopyCenteredCorrelation n N ν g j| ≤ ε := by
  rw [← apTwoCopyBoundedCutSystem_form n N ν g j hg]
  exact
    MajorizedCutSystem.abs_form_le_of_hasCFZCertificate
      hLF j
      (apTwoCopyBoundedCutSystem n N ν g j hg)
      (apTwoCopyBoundedCutSystem_hasCFZCertificate
        n N ν g j hg)
      hε hconvert

end Wikipedia.SzemeredisTheorem
