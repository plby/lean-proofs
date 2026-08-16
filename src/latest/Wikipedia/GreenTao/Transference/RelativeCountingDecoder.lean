import Wikipedia.GreenTao.Transference.RelativeCountingCertificate

/-!
# Stage decoders for relative-counting Cauchy--Schwarz recursion

Repeated applications of `MajorizedCutSystem.next` replace an external
parameter `P` by the left-associated tower

`(((P × (G × G)) × (G × G)) × ⋯)`.

The declarations below give this tower a stable stage-indexed name and
identify it with a base parameter together with a Boolean pair for every
coordinate already eliminated.  In the AP application the base parameter
is itself a Boolean pair, belonging to the distinguished omitted face.
Thus stage `r` is canonically a Boolean cube on `r + 1` axes.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The nested parameter tower -/

/-- The external parameter type after `r` applications of
`MajorizedCutSystem.next`.

The recursion changes the base type before recurring.  Consequently
`CSStageParam P G (r + 1)` is definitionally
`CSStageParam (P × (G × G)) G r`, exactly the type produced by applying
`next` once and then iterating `r` more times. -/
def CSStageParam (P G : Type u) :
    ℕ → Type u
  | 0 => P
  | r + 1 => CSStageParam (P × (G × G)) G r

/-- Reassociate the decoded successor parameter so that the newest pair
becomes the head of a `Fin (r + 1)` tuple. -/
def csStageDecodedSuccEquiv
    (P G : Type u) (r : ℕ) :
    ((P × (G × G)) × (Fin r → G × G)) ≃
      P × (Fin (r + 1) → G × G) where
  toFun q :=
    (q.1.1, Fin.cons q.1.2 q.2)
  invFun q :=
    ((q.1, q.2 0), Fin.tail q.2)
  left_inv q := by
    rcases q with ⟨⟨p, a⟩, rest⟩
    apply Prod.ext
    · exact Prod.ext rfl rfl
    · funext i
      rfl
  right_inv q := by
    rcases q with ⟨p, pairs⟩
    apply Prod.ext
    · rfl
    · exact Fin.cons_self_tail pairs

/-- Decode the nested `next` parameter into the original parameter and
one ordered pair for every eliminated coordinate. -/
def csStageParamEquiv
    (P G : Type u) :
    ∀ r : ℕ,
      CSStageParam P G r ≃
        P × (Fin r → G × G)
  | 0 =>
      { toFun := fun p => (p, fun i => Fin.elim0 i)
        invFun := fun q => q.1
        left_inv := fun _ => rfl
        right_inv := by
          intro q
          rcases q with ⟨p, empty⟩
          apply Prod.ext
          · rfl
          · funext i
            exact Fin.elim0 i }
  | r + 1 =>
      (csStageParamEquiv (P × (G × G)) G r).trans
        (csStageDecodedSuccEquiv P G r)

/-- Finiteness of a stage parameter is transported from its decoded
product representation. -/
noncomputable instance csStageParamFintype
    {P G : Type u} [Fintype P] [Fintype G] {r : ℕ} :
    Fintype (CSStageParam P G r) :=
  Fintype.ofEquiv
    (P × (Fin r → G × G))
    (csStageParamEquiv P G r).symm

/-- The original external parameter retained inside a stage parameter. -/
def CSStageParam.base
    {P G : Type u} {r : ℕ}
    (p : CSStageParam P G r) : P :=
  (csStageParamEquiv P G r p).1

/-- The ordered endpoint pair belonging to an already eliminated
coordinate. -/
def CSStageParam.pair
    {P G : Type u} {r : ℕ}
    (p : CSStageParam P G r) (i : Fin r) : G × G :=
  (csStageParamEquiv P G r p).2 i

/-- Reconstruct a nested stage parameter from its base and ordered endpoint
pairs. -/
def CSStageParam.ofDecoded
    {P G : Type u} {r : ℕ}
    (p : P) (a : Fin r → G × G) :
    CSStageParam P G r :=
  (csStageParamEquiv P G r).symm (p, a)

@[simp]
theorem CSStageParam.base_ofDecoded
    {P G : Type u} {r : ℕ}
    (p : P) (a : Fin r → G × G) :
    (CSStageParam.ofDecoded p a :
      CSStageParam P G r).base = p := by
  exact congrArg Prod.fst
    ((csStageParamEquiv P G r).apply_symm_apply (p, a))

@[simp]
theorem CSStageParam.pair_ofDecoded
    {P G : Type u} {r : ℕ}
    (p : P) (a : Fin r → G × G) (i : Fin r) :
    (CSStageParam.ofDecoded p a :
      CSStageParam P G r).pair i = a i := by
  exact congrFun
    (congrArg Prod.snd
      ((csStageParamEquiv P G r).apply_symm_apply (p, a))) i

@[simp]
theorem CSStageParam.ofDecoded_base_pair
    {P G : Type u} {r : ℕ}
    (p : CSStageParam P G r) :
    CSStageParam.ofDecoded p.base p.pair = p :=
  (csStageParamEquiv P G r).symm_apply_apply p

/-! ## Boolean-axis form of the AP parameter -/

/-- A base Boolean pair followed by `r` endpoint pairs is a Boolean cube
on `r + 1` ordered axes.  Axis zero is the original omitted AP coordinate;
axis `i.succ` is the `i`-th coordinate eliminated by Cauchy--Schwarz. -/
def csStageBooleanAxesEquiv
    (G : Type u) (r : ℕ) :
    ((Bool → G) × (Fin r → G × G)) ≃
      (Fin (r + 1) → Bool → G) where
  toFun q :=
    Fin.cons q.1
      (fun i => selectPair (q.2 i))
  invFun x :=
    (x 0,
      fun i => boolEndpointEquiv G (x i.succ))
  left_inv q := by
    rcases q with ⟨a, pairs⟩
    apply Prod.ext
    · rfl
    · funext i
      exact (boolEndpointEquiv G).right_inv (pairs i)
  right_inv x := by
    funext i
    refine Fin.cases rfl (fun t => ?_) i
    exact selectPair_boolEndpointEquiv (x t.succ)

/-- Decode the concrete AP parameter tower into its ordered Boolean axes. -/
def apCSStageParamEquiv
    (G : Type u) (r : ℕ) :
    CSStageParam (Bool → G) G r ≃
      (Fin (r + 1) → Bool → G) :=
  (csStageParamEquiv (Bool → G) G r).trans
    (csStageBooleanAxesEquiv G r)

@[simp]
theorem apCSStageParamEquiv_zero_apply
    (G : Type u) (a : Bool → G) :
    apCSStageParamEquiv G 0 a = fun _ => a := by
  funext i
  exact Fin.eq_zero i ▸ rfl

/-! ## Full AP cube decoder -/

/-- Split a doubled tuple into the distinguished coordinate and the
canonically ordered tuple of all other doubled coordinates. -/
def apProjectionAxesEquiv
    (G : Type u) (n : ℕ) (j : Fin (n + 1)) :
    (Fin (n + 1) → Bool → G) ≃
      (Bool → G) × (Fin n → Bool → G) where
  toFun x :=
    (x j, fun t => x (j.succAbove t))
  invFun q :=
    Fin.insertNth j q.1 q.2
  left_inv x := by
    apply (Fin.insertNth_eq_iff).2
    exact ⟨rfl, rfl⟩
  right_inv q := by
    rcases q with ⟨a, y⟩
    apply Prod.ext
    · funext b
      simp
    · funext t b
      simp

/-- Split the doubled deleted-coordinate tuple at Cauchy--Schwarz stage
`r`.

The output consists of:

* endpoint pairs for the `r` processed coordinates;
* the shared `false` values for the `s` future coordinates;
* the unused pair at the current coordinate;
* the unused `true` values for the future coordinates.

The deleted-coordinate count is `r + (s + 1)`: processed coordinates,
the current coordinate, and future coordinates. -/
def csStageDeletedAxesEquiv
    (G : Type u) (r s : ℕ) :
    (Fin (r + (s + 1)) → Bool → G) ≃
      (((Fin r → G × G) × (Fin s → G)) ×
        ((G × G) × (Fin s → G))) where
  toFun x :=
    (((fun i =>
        boolEndpointEquiv G
          (x (Fin.castAdd (s + 1) i))),
      fun t =>
        x (Fin.natAdd r t.succ) false),
    (boolEndpointEquiv G
        (x (Fin.natAdd r (0 : Fin (s + 1)))),
      fun t =>
        x (Fin.natAdd r t.succ) true))
  invFun q :=
    Fin.append
      (fun i => selectPair (q.1.1 i))
      (Fin.cons
        (selectPair q.2.1)
        (fun t b =>
          if b then q.2.2 t else q.1.2 t))
  left_inv x := by
    funext i b
    refine Fin.addCases (m := r) (n := s + 1) ?_ ?_ i
    · intro t
      dsimp only
      rw [Fin.append_left]
      exact congrFun
        (selectPair_boolEndpointEquiv
          (x (Fin.castAdd (s + 1) t))) b
    · intro t
      dsimp only
      rw [Fin.append_right]
      refine Fin.cases ?_ (fun q => ?_) t
      · exact congrFun
          (selectPair_boolEndpointEquiv
            (x (Fin.natAdd r (0 : Fin (s + 1))))) b
      · cases b <;> rfl
  right_inv q := by
    rcases q with
      ⟨⟨processed, futureFalse⟩,
        ⟨current, futureTrue⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        dsimp only
        rw [Fin.append_left]
        exact
          (boolEndpointEquiv G).right_inv
            (processed i)
      · funext t
        dsimp only
        rw [Fin.append_right]
        rfl
    · apply Prod.ext
      · dsimp only
        rw [Fin.append_right]
        exact
          (boolEndpointEquiv G).right_inv current
      · funext t
        dsimp only
        rw [Fin.append_right]
        rfl

/-- Decode a full AP Boolean cube at stage `r`, with `s + 1` live
deleted coordinates.

The first output component is precisely the parameter and live tail
averaged by `headMajorantMean`.  The second component consists entirely of
uniform fibers ignored by that moment: the current coordinate pair and the
future `true` tuple. -/
def apCSStageCubeEquiv
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1)) :
    CubePoint ((r + (s + 1)) + 1) N ≃
      ((CSStageParam (Bool → ZMod N) (ZMod N) r ×
          (Fin s → ZMod N)) ×
        ((ZMod N × ZMod N) × (Fin s → ZMod N))) := by
  let split :=
    (apProjectionAxesEquiv
      (ZMod N) (r + (s + 1)) j).trans
      (Equiv.prodCongr
        (Equiv.refl (Bool → ZMod N))
        (csStageDeletedAxesEquiv (ZMod N) r s))
  exact
    split.trans
      { toFun := fun q =>
          (((csStageParamEquiv
                (Bool → ZMod N) (ZMod N) r).symm
              (q.1, q.2.1.1),
            q.2.1.2),
          q.2.2)
        invFun := fun q =>
          let decoded :=
            csStageParamEquiv
              (Bool → ZMod N) (ZMod N) r q.1.1
          (decoded.1,
            ((decoded.2, q.1.2), q.2))
        left_inv := by
          intro q
          rcases q with
            ⟨a, ⟨⟨processed, futureFalse⟩, unused⟩⟩
          simp
        right_inv := by
          intro q
          rcases q with
            ⟨⟨p, futureFalse⟩, unused⟩
          simp }

@[simp]
theorem apCSStageCubeEquiv_base
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N) :
    (apCSStageCubeEquiv r s N j x).1.1.base =
      x j := by
  simp [apCSStageCubeEquiv, apProjectionAxesEquiv,
    csStageDeletedAxesEquiv, CSStageParam.base]

@[simp]
theorem apCSStageCubeEquiv_processedPair
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N)
    (i : Fin r) :
    (apCSStageCubeEquiv r s N j x).1.1.pair i =
      (x (j.succAbove (Fin.castAdd (s + 1) i)) false,
        x (j.succAbove (Fin.castAdd (s + 1) i)) true) := by
  simp [apCSStageCubeEquiv, apProjectionAxesEquiv,
    csStageDeletedAxesEquiv, CSStageParam.pair,
    boolEndpointEquiv]

@[simp]
theorem apCSStageCubeEquiv_futureFalse
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N)
    (t : Fin s) :
    (apCSStageCubeEquiv r s N j x).1.2 t =
      x (j.succAbove (Fin.natAdd r t.succ)) false := by
  rfl

@[simp]
theorem apCSStageCubeEquiv_currentPair
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N) :
    (apCSStageCubeEquiv r s N j x).2.1 =
      (x (j.succAbove
          (Fin.natAdd r (0 : Fin (s + 1)))) false,
        x (j.succAbove
          (Fin.natAdd r (0 : Fin (s + 1)))) true) := by
  rfl

@[simp]
theorem apCSStageCubeEquiv_futureTrue
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N)
    (t : Fin s) :
    (apCSStageCubeEquiv r s N j x).2.2 t =
      x (j.succAbove (Fin.natAdd r t.succ)) true := by
  rfl

/-! ## Expected CFZ selectors at a decoded stage -/

/-- The original simplex face whose deleted-coordinate factor is paid
after `r` coordinates have already been eliminated. -/
def apCSStageCurrentFace
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1)) :
    Fin ((r + (s + 1)) + 1) :=
  j.succAbove
    (Fin.natAdd r (0 : Fin (s + 1)))

/-- A selected vertex of the current face.

The Boolean assignment is free on the distinguished coordinate `j` and on
the `r` processed coordinates.  Every future coordinate is fixed to
`false`; the current face coordinate is absent from its own deleted cube. -/
noncomputable def apCSStageVertex
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (bits : Fin (r + 1) → Bool) :
    DeletedCube
      ((r + (s + 1)) + 1)
      (apCSStageCurrentFace r s j) :=
  fun i =>
    if hij : i.1 = j then
      bits 0
    else
      let t :=
        (finSuccAboveEquiv j).symm
          ⟨i.1, hij⟩
      if ht : t.val < r then
        bits (Fin.succ ⟨t.val, ht⟩)
      else
        false

/-- The exact one-face CFZ selector expected for the majorant moment at
stage `r`.  It is empty when the current face is inactive. -/
noncomputable def apCSStageFaceExponent
    (r s : ℕ)
    (active : Fin ((r + (s + 1)) + 1) → Bool)
    (j : Fin ((r + (s + 1)) + 1)) :
    LinearFormsExponent ((r + (s + 1)) + 1) :=
  faceLinearFormsExponent
    (apCSStageCurrentFace r s j)
    (fun ω =>
      if active (apCSStageCurrentFace r s j) then
        if ∃ bits : Fin (r + 1) → Bool,
            apCSStageVertex r s j bits = ω
        then true
        else false
      else false)

/-- At the terminal stage, every vertex on every active non-distinguished
face has been generated; the distinguished face remains reserved for the
centered factor. -/
def apCSActiveTerminalExponent
    {k : ℕ}
    (active : Fin k → Bool) (j : Fin k) :
    LinearFormsExponent k :=
  fun i _ω =>
    if i = j then false else active i

@[simp]
theorem apCSActiveTerminalExponent_distinguished
    {k : ℕ}
    (active : Fin k → Bool) (j : Fin k)
    (ω : DeletedCube k j) :
    apCSActiveTerminalExponent active j j ω = false := by
  simp [apCSActiveTerminalExponent]

/-- The stage decoder preserves normalized averages and discards exactly
the unused AP cube fibers. -/
theorem mean_apCSStageCubeEquiv
    (r s N : ℕ) [NeZero N]
    (j : Fin ((r + (s + 1)) + 1))
    (F :
      CSStageParam (Bool → ZMod N) (ZMod N) r →
        (Fin s → ZMod N) → ℝ) :
    mean₂ F =
      mean (fun x : CubePoint ((r + (s + 1)) + 1) N =>
        F (apCSStageCubeEquiv r s N j x).1.1
          (apCSStageCubeEquiv r s N j x).1.2) := by
  let unused :=
    (ZMod N × ZMod N) × (Fin s → ZMod N)
  calc
    mean₂ F =
        mean (fun q :
          CSStageParam
              (Bool → ZMod N) (ZMod N) r ×
            (Fin s → ZMod N) =>
          F q.1 q.2) :=
      (mean_prod_type F).symm
    _ =
        mean (fun q :
          (CSStageParam
              (Bool → ZMod N) (ZMod N) r ×
            (Fin s → ZMod N)) × unused =>
          F q.1.1 q.1.2) := by
      symm
      exact mean_prod_fst (β := unused)
        (fun q :
          CSStageParam
              (Bool → ZMod N) (ZMod N) r ×
            (Fin s → ZMod N) =>
          F q.1 q.2)
    _ = mean (fun x :
          CubePoint ((r + (s + 1)) + 1) N =>
        F (apCSStageCubeEquiv r s N j x).1.1
          (apCSStageCubeEquiv r s N j x).1.2) := by
      symm
      apply mean_equiv (apCSStageCubeEquiv r s N j)
      intro x
      rfl

/-! ## Iterating `MajorizedCutSystem.next` -/

namespace MajorizedCutSystem

/-- Change only the external parameterization of a cut system. -/
def reindex
    {P Q G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (e : Q ≃ P) :
    MajorizedCutSystem Q G n where
  core := fun q => S.core (e q)
  factor := fun q => S.factor (e q)
  majorant := fun q => S.majorant (e q)
  factor_nonneg := fun q => S.factor_nonneg (e q)
  factor_le_majorant := fun q => S.factor_le_majorant (e q)

@[simp]
theorem reindex_core
    {P Q G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (e : Q ≃ P) (q : Q) (x : Fin n → G) :
    (S.reindex e).core q x = S.core (e q) x :=
  rfl

@[simp]
theorem reindex_factor
    {P Q G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (e : Q ≃ P) (q : Q)
    (i : Fin n) (x : Fin (n - 1) → G) :
    (S.reindex e).factor q i x =
      S.factor (e q) i x :=
  rfl

@[simp]
theorem reindex_majorant
    {P Q G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (e : Q ≃ P) (q : Q)
    (i : Fin n) (x : Fin (n - 1) → G) :
    (S.reindex e).majorant q i x =
      S.majorant (e q) i x :=
  rfl

/-- Reindexing the finite external parameter does not change the represented
normalized cut form. -/
theorem reindex_form
    {P Q G : Type u}
    [Fintype P] [Fintype Q] [Fintype G]
    {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (e : Q ≃ P) :
    (S.reindex e).form = S.form := by
  unfold form mean₂ reindex
  apply mean_equiv e
  intro q
  rfl

/-- Reindexing the finite external parameter does not change the majorant
moment paid at the next Cauchy--Schwarz step. -/
theorem reindex_headMajorantMean
    {P Q G : Type u}
    [Fintype P] [Fintype Q] [Fintype G]
    {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (e : Q ≃ P) :
    (S.reindex e).headMajorantMean =
      S.headMajorantMean := by
  unfold headMajorantMean mean₂ reindex
  apply mean_equiv e
  intro q
  rfl

/-- Parameter reindexing commutes with one recursive transform. -/
theorem reindex_next
    {P Q G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (e : Q ≃ P) :
    (S.reindex e).next =
      S.next.reindex
        (Equiv.prodCongr e
          (Equiv.refl (G × G))) := by
  cases n <;> rfl

/-- A structural CFZ certificate is invariant under a finite equivalence of
the external parameter type. -/
theorem HasCFZCertificate.reindex
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k)
    {G : Type u} [Fintype G] :
    ∀ {P Q : Type u} [Fintype P] [Fintype Q]
      {n : ℕ}
      (S : MajorizedCutSystem P G n)
      (e : Q ≃ P),
      HasCFZCertificate ν j S →
        HasCFZCertificate ν j (S.reindex e) := by
  intro P Q instP instQ n
  induction n generalizing P Q with
  | zero =>
      intro S e hS
      rcases hS with ⟨other, hother, hform⟩
      refine ⟨other, hother, ?_⟩
      rw [reindex_form]
      exact hform
  | succ n ih =>
      intro S e hS
      rcases hS with ⟨selector, hmoment, hnext⟩
      refine ⟨selector, ?_, ?_⟩
      · rw [reindex_headMajorantMean]
        exact hmoment
      · rw [reindex_next]
        exact ih S.next
          (Equiv.prodCongr e
            (Equiv.refl (G × G)))
          hnext

/-- Apply `next` exactly `r` times to a system with `n + r` live
coordinates.  The result has the definitionally correct nested parameter
`CSStageParam P G r` and `n` remaining coordinates. -/
def iterNext
    {P G : Type u} {n : ℕ} :
    ∀ r : ℕ,
      MajorizedCutSystem P G (n + r) →
        MajorizedCutSystem (CSStageParam P G r) G n
  | 0, S => S
  | r + 1, S => iterNext r S.next

@[simp]
theorem iterNext_zero
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n) :
    iterNext 0 S = S :=
  rfl

@[simp]
theorem iterNext_succ
    {P G : Type u} {n r : ℕ}
    (S : MajorizedCutSystem P G (n + (r + 1))) :
    iterNext (r + 1) S =
      iterNext r S.next :=
  rfl

/-- At a completed stage, the parameter type is the initial parameter
together with one endpoint pair for every original coordinate. -/
def iterNextDecoded
    {P G : Type u} {n r : ℕ}
    (S : MajorizedCutSystem P G (n + r)) :
    MajorizedCutSystem
      (P × (Fin r → G × G)) G n :=
  (iterNext r S).reindex
    (csStageParamEquiv P G r).symm

/-- Decoding the nested stage parameter preserves the stage form. -/
theorem iterNextDecoded_form
    {P G : Type u}
    [Fintype P] [Fintype G]
    {n r : ℕ}
    (S : MajorizedCutSystem P G (n + r)) :
    (iterNextDecoded S).form =
      (iterNext r S).form :=
  reindex_form
    (iterNext r S)
    (csStageParamEquiv P G r).symm

/-- Decoding the nested stage parameter preserves its next paid moment. -/
theorem iterNextDecoded_headMajorantMean
    {P G : Type u}
    [Fintype P] [Fintype G]
    {n r : ℕ}
    (S : MajorizedCutSystem P G ((n + 1) + r)) :
    (iterNextDecoded S).headMajorantMean =
      (iterNext r S).headMajorantMean :=
  reindex_headMajorantMean
    (iterNext r S)
    (csStageParamEquiv P G r).symm

/-- The exact algebraic obligation at a decoded successor stage: its paid
majorant moment is one ordinary CFZ subproduct. -/
def HasDecodedCFZStageMoment
    {k N : ℕ} [NeZero N]
    (ν : ZMod N → ℝ)
    {P G : Type u}
    [Fintype P] [Fintype G]
    {n r : ℕ}
    (S : MajorizedCutSystem P G ((n + 1) + r)) :
    Prop :=
  ∃ selector : LinearFormsExponent k,
    (iterNextDecoded S).headMajorantMean =
      mean (linearFormsProduct k N ν selector)

/-- The decoded stage-moment obligation is exactly the original nested
stage obligation; no numerical factor or extra hypothesis is introduced by
the parameter equivalence. -/
theorem hasDecodedCFZStageMoment_iff
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {P G : Type u}
    [Fintype P] [Fintype G]
    {n r : ℕ}
    (S : MajorizedCutSystem P G ((n + 1) + r)) :
    HasDecodedCFZStageMoment (k := k) ν S ↔
      ∃ selector : LinearFormsExponent k,
        (iterNext r S).headMajorantMean =
          mean (linearFormsProduct k N ν selector) := by
  constructor
  · rintro ⟨selector, hselector⟩
    refine ⟨selector, ?_⟩
    rw [← iterNextDecoded_headMajorantMean S]
    exact hselector
  · rintro ⟨selector, hselector⟩
    refine ⟨selector, ?_⟩
    rw [iterNextDecoded_headMajorantMean S]
    exact hselector

/-- Any certificate for a nested stage transports to the decoded Boolean
pair representation. -/
theorem HasCFZCertificate.iterNextDecoded
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k)
    {P G : Type u}
    [Fintype P] [Fintype G]
    {n r : ℕ}
    (S : MajorizedCutSystem P G (n + r))
    (hS : HasCFZCertificate ν j
      (iterNext r S)) :
    HasCFZCertificate ν j
      (iterNextDecoded S) :=
  hS.reindex j
    (iterNext r S)
    (csStageParamEquiv P G r).symm

end MajorizedCutSystem

/-! ## Quantitative endpoint after the decoded first stage -/

/-- Root-extracted active-mask correlation bound once the recursively
decoded tail has its structural certificate.

The first mixed majorant moment is discharged by the exact isolated-face
identity in `RelativeCountingCertificate`; `hnext` is therefore precisely
the remaining stage-decoder obligation.  No additional analytic estimate
is assumed. -/
theorem HasLinearFormsCondition.abs_apTwoCopyCenteredCorrelation_le_of_masked_nextCertificate
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
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
          (m + 1) N ν active g j hrest).next)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |apTwoCopyCenteredCorrelation
        (m + 1) N ν g j| ≤ ε := by
  rw [← apTwoCopyMaskedMajorizedCutSystem_form
    (m + 1) N ν active g j hrest]
  exact
    MajorizedCutSystem.abs_form_le_of_hasCFZCertificate
      hLF j
      (apTwoCopyMaskedMajorizedCutSystem
        (m + 1) N ν active g j hrest)
      (apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate_of_next
        m N ν active g j hrest hnext)
      hε hconvert

end Wikipedia.SzemeredisTheorem
