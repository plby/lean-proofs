import Wikipedia.GreenTao.Transference.RelativeCountingDecoder

/-!
# Pointwise stage identities for relative counting

This file turns the stage equivalence from
`RelativeCountingDecoder` into closed formulas for the majorants generated
by repeated `MajorizedCutSystem.next`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Prefixing the processed endpoint choices -/

/-- Put `r` processed coordinate values in front of an `s`-coordinate
future tuple.  The apparently reversed length `s + r` is chosen because it
is definitionally compatible with recursion on `r`. -/
def csPrependTuple
    {G : Type u} {s : ℕ} :
    ∀ r : ℕ,
      (Fin r → G) → (Fin s → G) →
        (Fin (s + r) → G)
  | 0, _a, z => z
  | r + 1, a, z =>
      Fin.cons (a 0)
        (csPrependTuple r (Fin.tail a) z)

@[simp]
theorem csPrependTuple_zero
    {G : Type u} {s : ℕ}
    (a : Fin 0 → G) (z : Fin s → G) :
    csPrependTuple 0 a z = z :=
  rfl

@[simp]
theorem csPrependTuple_succ_zero
    {G : Type u} {r s : ℕ}
    (a : Fin (r + 1) → G) (z : Fin s → G) :
    csPrependTuple (r + 1) a z 0 = a 0 :=
  rfl

@[simp]
theorem csPrependTuple_succ_succ
    {G : Type u} {r s : ℕ}
    (a : Fin (r + 1) → G) (z : Fin s → G)
    (i : Fin (s + r)) :
    csPrependTuple (r + 1) a z i.succ =
      csPrependTuple r (Fin.tail a) z i :=
  rfl

/-- Add a head value to a possibly zero-dimensional tuple. -/
def csConsInput
    {G : Type u} :
    ∀ n : ℕ, G → (Fin (n - 1) → G) → Fin n → G
  | 0, _a, _z => fun i => Fin.elim0 i
  | _n + 1, a, z => Fin.cons a z

@[simp]
theorem csConsInput_succ
    {G : Type u} (n : ℕ)
    (a : G) (z : Fin n → G) :
    csConsInput (n + 1) a z = Fin.cons a z :=
  rfl

@[simp]
theorem csConsInput_apply_zero
    {G : Type u} (n : ℕ) (hn : 0 < n)
    (a : G) (z : Fin (n - 1) → G) :
    csConsInput n a z ⟨0, hn⟩ = a := by
  cases n with
  | zero => omega
  | succ _ => rfl

@[simp]
theorem csConsInput_apply_succ
    {G : Type u} (n : ℕ)
    (a : G) (z : Fin (n - 1) → G)
    (i : Fin (n - 1)) :
    csConsInput n a z ⟨i + 1, by omega⟩ =
      z i := by
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ _ =>
      rfl

/-- The original coordinate paid after `r` head coordinates have already
been eliminated. -/
def csOrderedStageCurrentIndex
    (r s : ℕ) :
    Fin ((s + 1) + r) :=
  ⟨r, by omega⟩

/-- Reconstruct the input to the original current-coordinate cut factor
from choices on the processed coordinates and the shared future tuple. -/
def csOrderedStageFactorInput
    {G : Type u} :
    ∀ r s : ℕ,
      (Fin r → G) → (Fin s → G) →
        (Fin (((s + 1) + r) - 1) → G)
  | 0, _s, _a, z => z
  | r + 1, s, a, z =>
      csConsInput ((s + 1) + r) (a 0)
        (csOrderedStageFactorInput r s
          (Fin.tail a) z)

@[simp]
theorem csOrderedStageFactorInput_zero
    {G : Type u} (s : ℕ)
    (a : Fin 0 → G) (z : Fin s → G) :
    csOrderedStageFactorInput 0 s a z = z :=
  rfl

@[simp]
theorem csOrderedStageFactorInput_succ
    {G : Type u} (r s : ℕ)
    (a : Fin (r + 1) → G) (z : Fin s → G) :
    csOrderedStageFactorInput (r + 1) s a z =
      csConsInput ((s + 1) + r) (a 0)
        (csOrderedStageFactorInput r s
          (Fin.tail a) z) :=
  rfl

@[simp]
theorem csOrderedStageFactorInput_processed
    {G : Type u} (r s : ℕ)
    (a : Fin r → G) (z : Fin s → G)
    (i : Fin r) :
    csOrderedStageFactorInput r s a z
        ⟨i, by omega⟩ =
      a i := by
  induction r with
  | zero =>
      exact Fin.elim0 i
  | succ r ih =>
      refine Fin.cases ?_ (fun q => ?_) i
      · rw [csOrderedStageFactorInput_succ]
        exact csConsInput_apply_zero
          ((s + 1) + r) (by omega) _ _
      · rw [csOrderedStageFactorInput_succ]
        let q' : Fin (((s + 1) + r) - 1) :=
          ⟨q, by omega⟩
        calc
          csConsInput ((s + 1) + r) (a 0)
              (csOrderedStageFactorInput r s
                (Fin.tail a) z) ⟨q + 1, by omega⟩ =
              csOrderedStageFactorInput r s
                (Fin.tail a) z q' := by
                exact csConsInput_apply_succ
                  ((s + 1) + r) (a 0)
                  (csOrderedStageFactorInput r s
                    (Fin.tail a) z) q'
          _ = Fin.tail a q := by
            exact ih (Fin.tail a) q
          _ = a q.succ := rfl

@[simp]
theorem csOrderedStageFactorInput_future
    {G : Type u} (r s : ℕ)
    (a : Fin r → G) (z : Fin s → G)
    (t : Fin s) :
    csOrderedStageFactorInput r s a z
        ⟨r + t, by omega⟩ =
      z t := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [csOrderedStageFactorInput_succ]
      let q : Fin (((s + 1) + r) - 1) :=
        ⟨r + t, by omega⟩
      have hcons :=
        csConsInput_apply_succ
          ((s + 1) + r) (a 0)
          (csOrderedStageFactorInput r s
            (Fin.tail a) z) q
      calc
        csConsInput ((s + 1) + r) (a 0)
            (csOrderedStageFactorInput r s
              (Fin.tail a) z)
            ⟨(r + 1) + t, by omega⟩ =
            csOrderedStageFactorInput r s
              (Fin.tail a) z q := by
                rw [show
                  (⟨(r + 1) + t, by omega⟩ :
                    Fin ((s + 1) + r)) =
                    ⟨q + 1, by omega⟩ by
                      apply Fin.ext
                      simp [q]
                      omega]
                exact hcons
        _ = z t := ih (Fin.tail a)

/-- Every shortened tuple is the deletion of a full tuple.  Supplying the
value at the restored coordinate avoids any inhabitedness assumption. -/
theorem exists_eraseCoordinate_eq
    {G : Type u} {n : ℕ}
    (i : Fin n) (a : G)
    (z : Fin (n - 1) → G) :
    ∃ y : Fin n → G, eraseCoordinate i y = z := by
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      exact
        ⟨Fin.insertNth i a z,
          eraseCoordinate_insertNth i a z⟩

/-- A coordinate other than the erased one has a unique shortened-tuple
preimage; this numerical form avoids imposing a successor normal form on
the ambient arity. -/
theorem exists_eraseCoordinate_preimage
    {G : Type u} {n : ℕ}
    (i t : Fin n) (hit : t ≠ i)
    (y : Fin n → G) :
    ∃ q : Fin (n - 1),
      eraseCoordinate i y q = y t ∧
        (if q.val < i.val then q.val else q.val + 1) =
          t.val := by
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      obtain ⟨q, hq⟩ :=
        Fin.exists_succAbove_eq hit
      refine ⟨q, ?_, ?_⟩
      · change y (i.succAbove q) = y t
        rw [hq]
      · have hv := congrArg Fin.val hq
        simpa only [Fin.succAbove, Fin.lt_def,
          apply_ite Fin.val, Fin.val_castSucc,
          Fin.val_succ] using hv

@[simp]
theorem tail_selectPair_cons
    {G : Type u} {r : ℕ}
    (a : Fin (r + 1) → G × G)
    (b : Bool) (bits : Fin r → Bool) :
    Fin.tail
        (fun i =>
          selectPair (a i)
            ((Fin.cons b bits :
              Fin (r + 1) → Bool) i)) =
      fun i =>
        selectPair (Fin.tail a i) (bits i) := by
  funext i
  rfl

/-! ## Closed formula for an iterated designated majorant -/

namespace MajorizedCutSystem

/-- The designated majorant field of `next`, uniformly across its
dimension-pattern branches. -/
@[simp]
theorem next_majorant_apply
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (a : G × G)
    (i : Fin n) (z : Fin (n - 1) → G) :
    S.next.majorant (p, a) i z =
      S.majorant p i.succ (csConsInput n a.1 z) *
        S.majorant p i.succ (csConsInput n a.2 z) := by
  cases n with
  | zero =>
      exact Fin.elim0 i
  | succ _ =>
      rfl

/-- After `r` recursive Cauchy--Schwarz steps, the current designated
majorant is the product of the original current-coordinate majorant over
all Boolean choices of the `r` processed endpoint pairs. -/
theorem iterNextDecoded_majorant_zero
    {P G : Type u} [Fintype P] [Fintype G]
    (r s : ℕ)
    (S : MajorizedCutSystem P G ((s + 1) + r))
    (p : P) (a : Fin r → G × G)
    (z : Fin s → G) :
    (iterNextDecoded S).majorant (p, a) 0 z =
      ∏ bits : Fin r → Bool,
        S.majorant p
          (csOrderedStageCurrentIndex r s)
          (csOrderedStageFactorInput r s
            (fun i => selectPair (a i) (bits i)) z) := by
  induction r generalizing P with
  | zero =>
      have hdecode :
          (csStageParamEquiv P G 0).symm (p, a) = p := by
        exact congrArg Prod.fst
          ((csStageParamEquiv P G 0).apply_symm_apply (p, a))
      simp [iterNextDecoded, iterNext, reindex,
        csOrderedStageCurrentIndex, hdecode]
  | succ r ih =>
      change
        (iterNextDecoded S.next).majorant
            ((p, a 0), Fin.tail a) 0 z =
          ∏ bits : Fin (r + 1) → Bool,
            S.majorant p
              (csOrderedStageCurrentIndex (r + 1) s)
              (csOrderedStageFactorInput (r + 1) s
                (fun i =>
                  selectPair (a i) (bits i)) z)
      rw [ih S.next (p, a 0) (Fin.tail a)]
      have hpoint (bits : Fin r → Bool) :
          S.next.majorant (p, a 0)
              (csOrderedStageCurrentIndex r s)
              (csOrderedStageFactorInput r s
                (fun i =>
                  selectPair (Fin.tail a i) (bits i)) z) =
            S.majorant p
                (csOrderedStageCurrentIndex (r + 1) s)
                (csOrderedStageFactorInput (r + 1) s
                  (fun i =>
                    selectPair (a i)
                      ((Fin.cons (false : Bool) bits :
                        Fin (r + 1) → Bool) i)) z) *
              S.majorant p
                (csOrderedStageCurrentIndex (r + 1) s)
                (csOrderedStageFactorInput (r + 1) s
                  (fun i =>
                    selectPair (a i)
                      ((Fin.cons (true : Bool) bits :
                        Fin (r + 1) → Bool) i)) z) := by
        rw [next_majorant_apply]
        apply congrArg₂ (· * ·)
        · apply congrArg₂
            (fun i x => S.majorant p i x)
          · apply Fin.ext
            rfl
          · funext q
            simp [csOrderedStageFactorInput,
              csConsInput]
        · apply congrArg₂
            (fun i x => S.majorant p i x)
          · apply Fin.ext
            rfl
          · funext q
            simp [csOrderedStageFactorInput,
              csConsInput]
      simp_rw [hpoint]
      rw [Finset.prod_mul_distrib]
      let F : Bool → (Fin r → Bool) → ℝ :=
        fun b bits =>
          S.majorant p
            (csOrderedStageCurrentIndex (r + 1) s)
            (csOrderedStageFactorInput (r + 1) s
              (fun i =>
                selectPair (a i)
                  ((Fin.cons b bits :
                    Fin (r + 1) → Bool) i)) z)
      have hreindex :
          (∏ bits : Fin (r + 1) → Bool,
              S.majorant p
                (csOrderedStageCurrentIndex (r + 1) s)
                (csOrderedStageFactorInput (r + 1) s
                  (fun i =>
                    selectPair (a i) (bits i)) z)) =
            ∏ q : Bool × (Fin r → Bool),
              F q.1 q.2 := by
        apply Fintype.prod_equiv
          (Fin.consEquiv
            (fun _ : Fin (r + 1) => Bool)).symm
        intro bits
        rfl
      rw [hreindex]
      rw [Fintype.prod_prod_type]
      rw [Fintype.prod_bool]
      ac_rfl

end MajorizedCutSystem

/-! ## The selected stage vertices -/

/-- The distinguished coordinate, regarded as a vertex coordinate of the
current non-distinguished face. -/
def apCSStageDistinguishedVertexIndex
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1)) :
    {i : Fin ((r + (s + 1)) + 1) //
      i ≠ apCSStageCurrentFace r s j} :=
  ⟨j, (Fin.succAbove_ne j
    (Fin.natAdd r (0 : Fin (s + 1)))).symm⟩

/-- A processed deleted coordinate, regarded as a vertex coordinate of the
current face. -/
def apCSStageProcessedVertexIndex
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (i : Fin r) :
    {q : Fin ((r + (s + 1)) + 1) //
      q ≠ apCSStageCurrentFace r s j} :=
  ⟨j.succAbove (Fin.castAdd (s + 1) i), by
    intro h
    have ht :=
      Fin.succAbove_right_injective (p := j) h
    have hv := congrArg Fin.val ht
    simp at hv
    omega⟩

@[simp]
theorem apCSStageVertex_distinguished
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (bits : Fin (r + 1) → Bool) :
    apCSStageVertex r s j bits
        (apCSStageDistinguishedVertexIndex r s j) =
      bits 0 := by
  simp [apCSStageVertex,
    apCSStageDistinguishedVertexIndex]

@[simp]
theorem apCSStageVertex_processed
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (bits : Fin (r + 1) → Bool)
    (i : Fin r) :
    apCSStageVertex r s j bits
        (apCSStageProcessedVertexIndex r s j i) =
      bits i.succ := by
  have ht :
      (finSuccAboveEquiv j).symm
          ⟨j.succAbove (Fin.castAdd (s + 1) i),
            Fin.succAbove_ne j
              (Fin.castAdd (s + 1) i)⟩ =
        Fin.castAdd (s + 1) i :=
    (finSuccAboveEquiv j).symm_apply_apply
      (Fin.castAdd (s + 1) i)
  simp [apCSStageVertex,
    apCSStageProcessedVertexIndex,
    Fin.succAbove_ne, ht]

/-- The stage-vertex map is injective: its distinguished value recovers
axis zero and its processed-coordinate values recover the tail axes. -/
theorem apCSStageVertex_injective
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1)) :
    Function.Injective
      (apCSStageVertex r s j) := by
  intro bits bits' hbits
  funext i
  refine Fin.cases ?_ (fun t => ?_) i
  · have h := congrFun hbits
      (apCSStageDistinguishedVertexIndex r s j)
    simpa using h
  · have h := congrFun hbits
      (apCSStageProcessedVertexIndex r s j t)
    simpa using h

/-- The Boolean assignments are equivalent to the subtype of selected
vertices used by `apCSStageFaceExponent`. -/
noncomputable def apCSStageVertexEquiv
    (r s : ℕ)
    (j : Fin ((r + (s + 1)) + 1)) :
    (Fin (r + 1) → Bool) ≃
      {ω : DeletedCube
          ((r + (s + 1)) + 1)
          (apCSStageCurrentFace r s j) //
        ∃ bits : Fin (r + 1) → Bool,
          apCSStageVertex r s j bits = ω} where
  toFun bits :=
    ⟨apCSStageVertex r s j bits,
      ⟨bits, rfl⟩⟩
  invFun ω :=
    Classical.choose ω.property
  left_inv bits := by
    apply apCSStageVertex_injective r s j
    exact Classical.choose_spec
      (show ∃ bits' : Fin (r + 1) → Bool,
          apCSStageVertex r s j bits' =
            apCSStageVertex r s j bits
        from ⟨bits, rfl⟩)
  right_inv ω := by
    apply Subtype.ext
    exact Classical.choose_spec ω.property

/-- Pointwise expansion of the expected stage selector. -/
theorem linearFormsProduct_apCSStageFaceExponent
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin ((r + (s + 1)) + 1) → Bool)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N) :
    linearFormsProduct ((r + (s + 1)) + 1) N ν
        (apCSStageFaceExponent r s active j) x =
      if active (apCSStageCurrentFace r s j) then
        ∏ bits : Fin (r + 1) → Bool,
          ν (apLinearForm
            ((r + (s + 1)) + 1) N
            (apCSStageCurrentFace r s j)
            (apCSStageVertex r s j bits) x)
      else 1 := by
  classical
  unfold apCSStageFaceExponent
  rw [← faceSelectedProduct_eq_linearFormsProduct]
  unfold cubeSelectedProduct faceFactorFamily
  cases hactive :
      active (apCSStageCurrentFace r s j) with
  | false =>
      simp
  | true =>
      simp only [if_true, Bool.ite_eq_true_distrib]
      simp only [Bool.false_eq_true, if_false_right, and_true]
      change
        (∏ ω : DeletedCube
            ((r + (s + 1)) + 1)
            (apCSStageCurrentFace r s j),
          if
            ∃ bits : Fin (r + 1) → Bool,
              apCSStageVertex r s j bits = ω
          then
            ν (apLinearForm
              ((r + (s + 1)) + 1) N
              (apCSStageCurrentFace r s j) ω x)
          else 1) =
          ∏ bits : Fin (r + 1) → Bool,
            ν (apLinearForm
              ((r + (s + 1)) + 1) N
              (apCSStageCurrentFace r s j)
              (apCSStageVertex r s j bits) x)
      rw [← Finset.prod_filter]
      rw [Finset.prod_subtype
        (p := fun ω :
          DeletedCube
            ((r + (s + 1)) + 1)
            (apCSStageCurrentFace r s j) =>
          ∃ bits : Fin (r + 1) → Bool,
            apCSStageVertex r s j bits = ω)
        (Finset.univ.filter fun ω :
          DeletedCube
            ((r + (s + 1)) + 1)
            (apCSStageCurrentFace r s j) =>
          ∃ bits : Fin (r + 1) → Bool,
            apCSStageVertex r s j bits = ω)
        (by simp)]
      symm
      apply Fintype.prod_equiv
        (apCSStageVertexEquiv r s j)
      intro bits
      rfl

/-! ## Transport from recursive to geometric coordinate order -/

/-- Equality of the two deleted-coordinate arity expressions. -/
theorem apCSStageDeletedArityEq (r s : ℕ) :
    (s + 1) + r =
      r + (s + 1) := by
  omega

/-- The recursive dimension expression and the geometric prefix expression
have the same value. -/
theorem apCSStageArityEq (r s : ℕ) :
    ((s + 1) + r) + 1 =
      (r + (s + 1)) + 1 :=
  congrArg (fun q => q + 1)
    (apCSStageDeletedArityEq r s)

/-- `Fin.cast` commutes with the canonical `succAbove` embedding. -/
theorem cast_succAbove
    {n m : ℕ} (h : n = m)
    (p : Fin (n + 1)) (i : Fin n) :
    Fin.cast (congrArg (fun q => q + 1) h)
        (p.succAbove i) =
      (Fin.cast (congrArg (fun q => q + 1) h) p).succAbove
        (Fin.cast h i) := by
  subst m
  rfl

/-- Transport the distinguished face from the recursive dimension order to
the geometric prefix order used by `apCSStageCubeEquiv`. -/
def apCSStageTransportJ
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    Fin ((r + (s + 1)) + 1) :=
  Fin.cast (apCSStageArityEq r s) j

/-- Transport an active-face mask to geometric prefix order. -/
def apCSStageTransportActive
    (r s : ℕ)
    (active : Fin (((s + 1) + r) + 1) → Bool) :
    Fin ((r + (s + 1)) + 1) → Bool :=
  fun i =>
    active (Fin.cast (apCSStageArityEq r s).symm i)

/-- Transport a full cube point across the arithmetic arity equality. -/
def apCSStageCubeTransportEquiv
    (r s N : ℕ) :
    CubePoint (((s + 1) + r) + 1) N ≃
      CubePoint ((r + (s + 1)) + 1) N :=
  Equiv.arrowCongr
    (finCongr (apCSStageArityEq r s))
    (Equiv.refl (Bool → ZMod N))

/-- The stage decoder with the original recursive arity exposed at its
domain. -/
def apCSOrderedStageCubeEquiv
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    CubePoint (((s + 1) + r) + 1) N ≃
      ((CSStageParam (Bool → ZMod N) (ZMod N) r ×
          (Fin s → ZMod N)) ×
        ((ZMod N × ZMod N) × (Fin s → ZMod N))) :=
  (apCSStageCubeTransportEquiv r s N).trans
    (apCSStageCubeEquiv r s N
      (apCSStageTransportJ r s j))

/-- The `i`-th processed deleted coordinate in recursive arity order. -/
def csOrderedStageProcessedIndex
    (r s : ℕ) (i : Fin r) :
    Fin ((s + 1) + r) :=
  ⟨i, by omega⟩

/-- The `t`-th future deleted coordinate in recursive arity order. -/
def csOrderedStageFutureIndex
    (r s : ℕ) (t : Fin s) :
    Fin ((s + 1) + r) :=
  ⟨r + 1 + t, by omega⟩

@[simp]
theorem apCSOrderedStageCubeEquiv_base
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N) :
    (apCSOrderedStageCubeEquiv r s N j x).1.1.base =
      x j := by
  simp [apCSOrderedStageCubeEquiv,
    apCSStageCubeTransportEquiv,
    apCSStageTransportJ]

@[simp]
theorem apCSOrderedStageCubeEquiv_processedPair
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N)
    (i : Fin r) :
    (apCSOrderedStageCubeEquiv r s N j x).1.1.pair i =
      (x (j.succAbove
          (csOrderedStageProcessedIndex r s i)) false,
        x (j.succAbove
          (csOrderedStageProcessedIndex r s i)) true) := by
  change
    (apCSStageCubeEquiv r s N
        (apCSStageTransportJ r s j)
        (apCSStageCubeTransportEquiv r s N x)).1.1.pair i =
      _
  rw [apCSStageCubeEquiv_processedPair]
  apply Prod.ext
  · apply congrArg
      (fun q =>
        x q false)
    apply Fin.ext
    have hindex :
        Fin.cast (apCSStageDeletedArityEq r s)
            (csOrderedStageProcessedIndex r s i) =
          Fin.castAdd (s + 1) i := by
      apply Fin.ext
      rfl
    have hsucc :=
      cast_succAbove
        (apCSStageDeletedArityEq r s) j
        (csOrderedStageProcessedIndex r s i)
    rw [hindex] at hsucc
    have hv := congrArg Fin.val hsucc
    simpa [apCSStageTransportJ] using hv.symm
  · apply congrArg
      (fun q =>
        x q true)
    apply Fin.ext
    have hindex :
        Fin.cast (apCSStageDeletedArityEq r s)
            (csOrderedStageProcessedIndex r s i) =
          Fin.castAdd (s + 1) i := by
      apply Fin.ext
      rfl
    have hsucc :=
      cast_succAbove
        (apCSStageDeletedArityEq r s) j
        (csOrderedStageProcessedIndex r s i)
    rw [hindex] at hsucc
    have hv := congrArg Fin.val hsucc
    simpa [apCSStageTransportJ] using hv.symm

@[simp]
theorem apCSOrderedStageCubeEquiv_futureFalse
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N)
    (t : Fin s) :
    (apCSOrderedStageCubeEquiv r s N j x).1.2 t =
      x (j.succAbove
        (csOrderedStageFutureIndex r s t)) false := by
  change
    (apCSStageCubeEquiv r s N
        (apCSStageTransportJ r s j)
        (apCSStageCubeTransportEquiv r s N x)).1.2 t =
      _
  rw [apCSStageCubeEquiv_futureFalse]
  apply congrArg (fun q => x q false)
  apply Fin.ext
  have hindex :
      Fin.cast (apCSStageDeletedArityEq r s)
          (csOrderedStageFutureIndex r s t) =
        Fin.natAdd r t.succ := by
    apply Fin.ext
    simp [csOrderedStageFutureIndex]
    omega
  have hsucc :=
    cast_succAbove
      (apCSStageDeletedArityEq r s) j
      (csOrderedStageFutureIndex r s t)
  rw [hindex] at hsucc
  have hv := congrArg Fin.val hsucc
  simpa [apCSStageTransportJ] using hv.symm

@[simp]
theorem apCSStageTransportActive_transportJ
    (r s : ℕ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1)) :
    apCSStageTransportActive r s active
        (apCSStageTransportJ r s j) =
      active j := by
  simp [apCSStageTransportActive,
    apCSStageTransportJ]

/-! ## The same selector in recursive arity order -/

/-- Current face in the original recursive arity order. -/
def apCSOrderedStageCurrentFace
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    Fin (((s + 1) + r) + 1) :=
  j.succAbove (csOrderedStageCurrentIndex r s)

/-- Current-face vertex in recursive arity order. -/
noncomputable def apCSOrderedStageVertex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool) :
    DeletedCube
      (((s + 1) + r) + 1)
      (apCSOrderedStageCurrentFace r s j) :=
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

def apCSOrderedStageDistinguishedVertexIndex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    {i : Fin (((s + 1) + r) + 1) //
      i ≠ apCSOrderedStageCurrentFace r s j} :=
  ⟨j, (Fin.succAbove_ne j
    (csOrderedStageCurrentIndex r s)).symm⟩

def apCSOrderedStageProcessedVertexIndex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (i : Fin r) :
    {q : Fin (((s + 1) + r) + 1) //
      q ≠ apCSOrderedStageCurrentFace r s j} :=
  ⟨j.succAbove (csOrderedStageProcessedIndex r s i), by
    intro h
    have ht :=
      Fin.succAbove_right_injective (p := j) h
    have hv := congrArg Fin.val ht
    simp [csOrderedStageProcessedIndex,
      csOrderedStageCurrentIndex] at hv
    omega⟩

def apCSOrderedStageFutureVertexIndex
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (t : Fin s) :
    {q : Fin (((s + 1) + r) + 1) //
      q ≠ apCSOrderedStageCurrentFace r s j} :=
  ⟨j.succAbove (csOrderedStageFutureIndex r s t), by
    intro h
    have ht :=
      Fin.succAbove_right_injective (p := j) h
    have hv := congrArg Fin.val ht
    simp [csOrderedStageFutureIndex,
      csOrderedStageCurrentIndex] at hv
    omega⟩

@[simp]
theorem apCSOrderedStageVertex_distinguished
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool) :
    apCSOrderedStageVertex r s j bits
        (apCSOrderedStageDistinguishedVertexIndex r s j) =
      bits 0 := by
  simp [apCSOrderedStageVertex,
    apCSOrderedStageDistinguishedVertexIndex]

@[simp]
theorem apCSOrderedStageVertex_processed
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool)
    (i : Fin r) :
    apCSOrderedStageVertex r s j bits
        (apCSOrderedStageProcessedVertexIndex r s j i) =
      bits i.succ := by
  unfold apCSOrderedStageVertex
  rw [dif_neg]
  · dsimp only [apCSOrderedStageProcessedVertexIndex]
    have ht :
        (finSuccAboveEquiv j).symm
            ⟨j.succAbove
                (csOrderedStageProcessedIndex r s i),
              Fin.succAbove_ne j
                (csOrderedStageProcessedIndex r s i)⟩ =
          csOrderedStageProcessedIndex r s i :=
      (finSuccAboveEquiv j).symm_apply_apply
        (csOrderedStageProcessedIndex r s i)
    rw [ht]
    simp [csOrderedStageProcessedIndex]
  · exact Fin.succAbove_ne j
      (csOrderedStageProcessedIndex r s i)

@[simp]
theorem apCSOrderedStageVertex_future
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (bits : Fin (r + 1) → Bool)
    (t : Fin s) :
    apCSOrderedStageVertex r s j bits
        (apCSOrderedStageFutureVertexIndex r s j t) =
      false := by
  unfold apCSOrderedStageVertex
  rw [dif_neg]
  · dsimp only [apCSOrderedStageFutureVertexIndex]
    have ht :
        (finSuccAboveEquiv j).symm
            ⟨j.succAbove
                (csOrderedStageFutureIndex r s t),
              Fin.succAbove_ne j
                (csOrderedStageFutureIndex r s t)⟩ =
          csOrderedStageFutureIndex r s t :=
      (finSuccAboveEquiv j).symm_apply_apply
        (csOrderedStageFutureIndex r s t)
    rw [ht]
    rw [dif_neg]
    simp
    simp [csOrderedStageFutureIndex]
    omega
  · exact Fin.succAbove_ne j
      (csOrderedStageFutureIndex r s t)

theorem apCSOrderedStageVertex_injective
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    Function.Injective
      (apCSOrderedStageVertex r s j) := by
  intro bits bits' hbits
  funext i
  refine Fin.cases ?_ (fun t => ?_) i
  · have h := congrFun hbits
      (apCSOrderedStageDistinguishedVertexIndex r s j)
    simpa using h
  · have h := congrFun hbits
      (apCSOrderedStageProcessedVertexIndex r s j t)
    simpa using h

noncomputable def apCSOrderedStageVertexEquiv
    (r s : ℕ)
    (j : Fin (((s + 1) + r) + 1)) :
    (Fin (r + 1) → Bool) ≃
      {ω : DeletedCube
          (((s + 1) + r) + 1)
          (apCSOrderedStageCurrentFace r s j) //
        ∃ bits : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits = ω} where
  toFun bits :=
    ⟨apCSOrderedStageVertex r s j bits,
      ⟨bits, rfl⟩⟩
  invFun ω :=
    Classical.choose ω.property
  left_inv bits := by
    apply apCSOrderedStageVertex_injective r s j
    exact Classical.choose_spec
      (show ∃ bits' : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits' =
            apCSOrderedStageVertex r s j bits
        from ⟨bits, rfl⟩)
  right_inv ω := by
    apply Subtype.ext
    exact Classical.choose_spec ω.property

/-- The reconstructed current-face AP form is the CFZ form at the
corresponding ordered-stage Boolean vertex. -/
theorem apSimplexForm_eq_apLinearForm_csOrderedStageVertex
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N)
    (bits : Fin r → Bool) (b : Bool)
    (y : Fin ((s + 1) + r) → ZMod N)
    (hy :
      eraseCoordinate (csOrderedStageCurrentIndex r s) y =
        csOrderedStageFactorInput r s
          (fun i =>
            x (j.succAbove
              (csOrderedStageProcessedIndex r s i))
              (bits i))
          (fun t =>
            x (j.succAbove
              (csOrderedStageFutureIndex r s t))
              false)) :
    apSimplexForm (((s + 1) + r) + 1) N
        (apCSOrderedStageCurrentFace r s j)
        (deleteCoordinate
          (Fin.insertNth j (x j b) y)
          (apCSOrderedStageCurrentFace r s j)) =
      apLinearForm (((s + 1) + r) + 1) N
        (apCSOrderedStageCurrentFace r s j)
        (apCSOrderedStageVertex r s j
          (Fin.cons b bits)) x := by
  unfold apSimplexForm apLinearForm
  apply Fintype.sum_congr
  intro i
  apply congrArg
    (fun z : ZMod N =>
      ((((i.1 : ℤ) -
        (apCSOrderedStageCurrentFace r s j : ℤ) : ℤ) :
          ZMod N) * z))
  change
    (@Fin.insertNth ((s + 1) + r)
      (fun _ => ZMod N) j (x j b) y i.1) =
      x i.1
        (apCSOrderedStageVertex r s j
          (Fin.cons b bits) i)
  by_cases hij : i.1 = j
  · rw [hij]
    simp only [Fin.insertNth_apply_same]
    unfold apCSOrderedStageVertex
    rw [dif_pos hij]
    rfl
  · let t :=
      (finSuccAboveEquiv j).symm
        ⟨i.1, hij⟩
    have hjt :
        j.succAbove t = i.1 := by
      have h :=
        congrArg Subtype.val
          ((finSuccAboveEquiv j).apply_symm_apply
            ⟨i.1, hij⟩)
      exact h
    have htne :
        t ≠ csOrderedStageCurrentIndex r s := by
      intro ht
      apply i.2
      rw [← hjt, ht]
      rfl
    obtain ⟨q, hqy, hval⟩ :=
      exists_eraseCoordinate_preimage
        (csOrderedStageCurrentIndex r s) t htne y
    have hfactor :
        csOrderedStageFactorInput r s
            (fun p =>
              x (j.succAbove
                (csOrderedStageProcessedIndex r s p))
                (bits p))
            (fun u =>
              x (j.succAbove
                (csOrderedStageFutureIndex r s u))
                false) q =
          y t :=
      (congrFun hy q).symm.trans hqy
    have hinsert :
        (@Fin.insertNth ((s + 1) + r)
          (fun _ => ZMod N) j (x j b) y i.1) =
          y t := by
      rw [← hjt]
      simp
    rw [hinsert]
    by_cases hq : q.val < r
    · let p : Fin r := ⟨q.val, hq⟩
      have htval : t.val = q.val := by
        simp [csOrderedStageCurrentIndex, hq] at hval
        omega
      have ht :
          t = csOrderedStageProcessedIndex r s p := by
        apply Fin.ext
        simpa [p, csOrderedStageProcessedIndex]
          using htval
      have hi :
          i =
            apCSOrderedStageProcessedVertexIndex
              r s j p := by
        apply Subtype.ext
        change
          i.1 =
            j.succAbove
              (csOrderedStageProcessedIndex r s p)
        rw [← hjt, ht]
      have hqindex :
          q =
            (⟨p.val, by omega⟩ :
              Fin (((s + 1) + r) - 1)) := by
        apply Fin.ext
        rfl
      rw [hi, ← hfactor, hqindex]
      rw [csOrderedStageFactorInput_processed]
      apply congrArg
        (x (j.succAbove
          (csOrderedStageProcessedIndex r s p)))
      symm
      simp
    · let u : Fin s :=
        ⟨q.val - r, by omega⟩
      have htval : t.val = q.val + 1 := by
        simp [csOrderedStageCurrentIndex, hq] at hval
        omega
      have ht :
          t = csOrderedStageFutureIndex r s u := by
        apply Fin.ext
        simp [u, csOrderedStageFutureIndex]
        omega
      have hi :
          i =
            apCSOrderedStageFutureVertexIndex
              r s j u := by
        apply Subtype.ext
        change
          i.1 =
            j.succAbove
              (csOrderedStageFutureIndex r s u)
        rw [← hjt, ht]
      have hqindex :
          q =
            (⟨r + u.val, by omega⟩ :
              Fin (((s + 1) + r) - 1)) := by
        apply Fin.ext
        simp [u]
        omega
      rw [hi, ← hfactor, hqindex]
      rw [csOrderedStageFactorInput_future]
      apply congrArg
        (x (j.succAbove
          (csOrderedStageFutureIndex r s u)))
      exact
        (apCSOrderedStageVertex_future
          r s j (Fin.cons b bits) u).symm

/-- One original designated cut factor, evaluated on the decoded stage
tuple, is precisely the product over the two new Boolean choices at the
current face. -/
theorem apTwoCopyMaskedMajorant_stageFactor
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (x : CubePoint (((s + 1) + r) + 1) N)
    (bits : Fin r → Bool) :
    (apTwoCopyMaskedMajorizedCutSystem
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
        apMaskedFaceMajorant ν active
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
        (fun _ => apMaskedFaceMajorant ν active)
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
    (apMaskedFaceMajorant ν active
      (apCSOrderedStageCurrentFace r s j))
  exact
    apSimplexForm_eq_apLinearForm_csOrderedStageVertex
      r s N j x bits b y hy'

/-- Expected stage selector, written without any arity casts. -/
noncomputable def apCSOrderedStageFaceExponent
    (r s : ℕ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1)) :
    LinearFormsExponent (((s + 1) + r) + 1) :=
  faceLinearFormsExponent
    (apCSOrderedStageCurrentFace r s j)
    (fun ω =>
      if active (apCSOrderedStageCurrentFace r s j) then
        if ∃ bits : Fin (r + 1) → Bool,
            apCSOrderedStageVertex r s j bits = ω
        then true
        else false
      else false)

/-- Pointwise expansion of the recursive-order stage selector. -/
theorem linearFormsProduct_apCSOrderedStageFaceExponent
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N) :
    linearFormsProduct (((s + 1) + r) + 1) N ν
        (apCSOrderedStageFaceExponent r s active j) x =
      if active (apCSOrderedStageCurrentFace r s j) then
        ∏ bits : Fin (r + 1) → Bool,
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j bits) x)
      else 1 := by
  classical
  unfold apCSOrderedStageFaceExponent
  rw [← faceSelectedProduct_eq_linearFormsProduct]
  unfold cubeSelectedProduct faceFactorFamily
  cases hactive :
      active (apCSOrderedStageCurrentFace r s j) with
  | false =>
      simp
  | true =>
      simp only [if_true, Bool.ite_eq_true_distrib]
      simp only [Bool.false_eq_true, if_false_right, and_true]
      change
        (∏ ω : DeletedCube
            (((s + 1) + r) + 1)
            (apCSOrderedStageCurrentFace r s j),
          if
            ∃ bits : Fin (r + 1) → Bool,
              apCSOrderedStageVertex r s j bits = ω
          then
            ν (apLinearForm
              (((s + 1) + r) + 1) N
              (apCSOrderedStageCurrentFace r s j) ω x)
          else 1) =
          ∏ bits : Fin (r + 1) → Bool,
            ν (apLinearForm
              (((s + 1) + r) + 1) N
              (apCSOrderedStageCurrentFace r s j)
              (apCSOrderedStageVertex r s j bits) x)
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
      rfl

/-- Successor-stage pointwise identity in the original recursive arity.
The transported distinguished coordinate and active mask are both
explicit, while `j'` is the current non-distinguished face
`j.succAbove ⟨r, _⟩`. -/
theorem iterNextDecoded_apTwoCopyMasked_majorant_zero
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (x : CubePoint (((s + 1) + r) + 1) N) :
    (MajorizedCutSystem.iterNextDecoded
        (apTwoCopyMaskedMajorizedCutSystem
          ((s + 1) + r) N ν active g j hrest)).majorant
        ((apCSOrderedStageCubeEquiv
          r s N j x).1.1.base,
          (apCSOrderedStageCubeEquiv
            r s N j x).1.1.pair)
        0
        (apCSOrderedStageCubeEquiv
          r s N j x).1.2 =
      linearFormsProduct (((s + 1) + r) + 1) N ν
        (apCSOrderedStageFaceExponent
          r s active j) x := by
  classical
  rw [
    MajorizedCutSystem.iterNextDecoded_majorant_zero]
  rw [linearFormsProduct_apCSOrderedStageFaceExponent]
  cases hactive :
      active (apCSOrderedStageCurrentFace r s j) with
  | false =>
      apply Fintype.prod_eq_one
      intro bits
      rw [apTwoCopyMaskedMajorant_stageFactor]
      apply Fintype.prod_eq_one
      intro b
      exact apMaskedFaceMajorant_of_inactive
        ν active
        (apCSOrderedStageCurrentFace r s j) _ hactive
  | true =>
      simp only [if_true]
      simp_rw [apTwoCopyMaskedMajorant_stageFactor]
      simp_rw [apMaskedFaceMajorant_of_active
        ν active
        (apCSOrderedStageCurrentFace r s j) _ hactive]
      let F :
          Bool → (Fin r → Bool) → ℝ :=
        fun b bits =>
          ν (apLinearForm
            (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j
              (Fin.cons b bits)) x)
      have hreindex :
          (∏ bits : Fin (r + 1) → Bool,
            ν (apLinearForm
              (((s + 1) + r) + 1) N
              (apCSOrderedStageCurrentFace r s j)
              (apCSOrderedStageVertex r s j bits) x)) =
            ∏ q : Bool × (Fin r → Bool),
              F q.1 q.2 := by
        apply Fintype.prod_equiv
          (Fin.consEquiv
            (fun _ : Fin (r + 1) => Bool)).symm
        intro bits
        rfl
      rw [hreindex, Fintype.prod_prod_type]
      rw [Finset.prod_comm]

/-- Recursive-order form of the stage decoder's mean-preservation
identity. -/
theorem mean_apCSOrderedStageCubeEquiv
    (r s N : ℕ) [NeZero N]
    (j : Fin (((s + 1) + r) + 1))
    (F :
      CSStageParam (Bool → ZMod N) (ZMod N) r →
        (Fin s → ZMod N) → ℝ) :
    mean₂ F =
      mean (fun x :
        CubePoint (((s + 1) + r) + 1) N =>
        F (apCSOrderedStageCubeEquiv
            r s N j x).1.1
          (apCSOrderedStageCubeEquiv
            r s N j x).1.2) := by
  calc
    mean₂ F =
        mean (fun x :
          CubePoint ((r + (s + 1)) + 1) N =>
          F (apCSStageCubeEquiv r s N
              (apCSStageTransportJ r s j) x).1.1
            (apCSStageCubeEquiv r s N
              (apCSStageTransportJ r s j) x).1.2) :=
      mean_apCSStageCubeEquiv r s N
        (apCSStageTransportJ r s j) F
    _ =
        mean (fun x :
          CubePoint (((s + 1) + r) + 1) N =>
          F (apCSOrderedStageCubeEquiv
              r s N j x).1.1
            (apCSOrderedStageCubeEquiv
              r s N j x).1.2) := by
      symm
      apply mean_equiv
        (apCSStageCubeTransportEquiv r s N)
      intro x
      rfl

/-- Decode both the nested stage parameter and the AP cube without
changing the next paid majorant moment. -/
theorem iterNextDecoded_headMajorantMean_eq_orderedCubeMean
    (r s N : ℕ) [NeZero N]
    (j : Fin (((s + 1) + r) + 1))
    (S : MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) ((s + 1) + r)) :
    (MajorizedCutSystem.iterNextDecoded S).headMajorantMean =
      mean (fun x :
        CubePoint (((s + 1) + r) + 1) N =>
        (MajorizedCutSystem.iterNextDecoded S).majorant
          ((apCSOrderedStageCubeEquiv
            r s N j x).1.1.base,
            (apCSOrderedStageCubeEquiv
              r s N j x).1.1.pair)
          0
          (apCSOrderedStageCubeEquiv
            r s N j x).1.2) := by
  let F :
      CSStageParam (Bool → ZMod N) (ZMod N) r →
        (Fin s → ZMod N) → ℝ :=
    fun p z =>
      (MajorizedCutSystem.iterNextDecoded S).majorant
        (p.base, p.pair) 0 z
  unfold MajorizedCutSystem.headMajorantMean
  calc
    mean₂ (fun p :
        (Bool → ZMod N) ×
          (Fin r → ZMod N × ZMod N) =>
        fun z =>
          (MajorizedCutSystem.iterNextDecoded S).majorant
            p 0 z) =
        mean₂ F := by
      unfold mean₂
      symm
      apply mean_equiv
        (csStageParamEquiv
          (Bool → ZMod N) (ZMod N) r)
      intro p
      rfl
    _ = _ :=
      mean_apCSOrderedStageCubeEquiv
        r s N j F

/-- The decoded successor paid moment is exactly the ordinary CFZ
subproduct selected by the current active face. -/
theorem iterNextDecoded_apTwoCopyMasked_headMajorantMean
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    (MajorizedCutSystem.iterNextDecoded
      (apTwoCopyMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)).headMajorantMean =
      mean (linearFormsProduct
        (((s + 1) + r) + 1) N ν
        (apCSOrderedStageFaceExponent
          r s active j)) := by
  rw [
    iterNextDecoded_headMajorantMean_eq_orderedCubeMean
      r s N j]
  apply congrArg mean
  funext x
  exact
    iterNextDecoded_apTwoCopyMasked_majorant_zero
      r s N ν active g j hrest x

/-- The same successor identity for the actual nested `next` tower. -/
theorem iterNext_apTwoCopyMasked_headMajorantMean
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    (MajorizedCutSystem.iterNext r
      (apTwoCopyMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)).headMajorantMean =
      mean (linearFormsProduct
        (((s + 1) + r) + 1) N ν
        (apCSOrderedStageFaceExponent
          r s active j)) := by
  rw [←
    MajorizedCutSystem.iterNextDecoded_headMajorantMean
      (apTwoCopyMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest)]
  exact
    iterNextDecoded_apTwoCopyMasked_headMajorantMean
      r s N ν active g j hrest

/-- Unconditional discharged decoded-stage obligation for the mixed
active-mask AP system. -/
theorem apTwoCopyMasked_hasDecodedCFZStageMoment
    (r s N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    MajorizedCutSystem.HasDecodedCFZStageMoment
      (k := ((s + 1) + r) + 1) ν
      (apTwoCopyMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest) := by
  exact
    ⟨apCSOrderedStageFaceExponent r s active j,
      iterNextDecoded_apTwoCopyMasked_headMajorantMean
        r s N ν active g j hrest⟩

end Wikipedia.SzemeredisTheorem
