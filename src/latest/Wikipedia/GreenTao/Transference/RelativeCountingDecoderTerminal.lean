import Wikipedia.GreenTao.Transference.RelativeCountingDecoderStep

/-!
# Terminal identities for the relative-counting decoder

This file closes the algebraic end of the mixed Cauchy--Schwarz recursion.
After every deleted coordinate has been doubled, the nested parameter is a
full Boolean AP cube.  The terminal core consists of the centered product
on the distinguished face and one copy of every vertex on each active
non-distinguished face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem

/-- Reindexing by the identity equivalence changes neither data nor
certificate-bearing structure. -/
@[simp]
theorem reindex_refl
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n) :
    S.reindex (Equiv.refl P) = S := by
  cases S
  rfl

/-- Product of all Boolean copies of the original core at a fully decoded
terminal parameter. -/
noncomputable def terminalCoreProduct
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (p : P) (a : Fin n → G × G) : ℝ :=
  ∏ bits : Fin n → Bool,
    S.core p (fun i => selectPair (a i) (bits i))

/-- Product of every original designated majorant at every vertex of its
deleted-coordinate cube. -/
noncomputable def terminalMajorantProduct
    {P G : Type u} :
    ∀ {n : ℕ},
      MajorizedCutSystem P G n →
      P → (Fin n → G × G) → ℝ
  | 0, _S, _p, _a => 1
  | n + 1, S, p, a =>
      ∏ i : Fin (n + 1),
        ∏ bits : Fin n → Bool,
          S.majorant p i
            (eraseCoordinate i
              (fun q =>
                selectPair (a q)
                  (@Fin.insertNth n
                    (fun _ => Bool) i false bits q)))

@[simp]
theorem terminalMajorantProduct_zero
    {P G : Type u}
    (S : MajorizedCutSystem P G 0)
    (p : P) (a : Fin 0 → G × G) :
    terminalMajorantProduct S p a = 1 :=
  rfl

@[simp]
theorem terminalMajorantProduct_succ
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (a : Fin (n + 1) → G × G) :
    terminalMajorantProduct S p a =
      ∏ i : Fin (n + 1),
        ∏ bits : Fin n → Bool,
          S.majorant p i
            (eraseCoordinate i
              (fun q =>
                selectPair (a q)
                  (@Fin.insertNth n
                    (fun _ => Bool) i false bits q))) :=
  rfl

/-- Apply `next` through every live coordinate, without introducing the
`0 + n` cast required by the more general two-index iterator. -/
def iterNextTerminal
    {P G : Type u} :
    ∀ n : ℕ,
      MajorizedCutSystem P G n →
        MajorizedCutSystem (CSStageParam P G n) G 0
  | 0, S => S
  | n + 1, S => iterNextTerminal n S.next

/-- The fully iterated system with its nested parameter decoded into the
original parameter and one endpoint pair for each eliminated coordinate. -/
def iterNextTerminalDecoded
    {P G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n) :
    MajorizedCutSystem (P × (Fin n → G × G)) G 0 :=
  (iterNextTerminal n S).reindex
    (csStageParamEquiv P G n).symm

/-- Transport only the live-coordinate arity of a cut system. -/
def castArity
    {P G : Type u} {m n : ℕ}
    (h : m = n)
    (S : MajorizedCutSystem P G m) :
    MajorizedCutSystem P G n :=
  h ▸ S

/-- Arity transport commutes with one recursive transform. -/
theorem castArity_next
    {P G : Type u} {m n : ℕ}
    (h : m = n)
    (S : MajorizedCutSystem P G (m + 1)) :
    (castArity (congrArg (· + 1) h) S).next =
      castArity h S.next := by
  subst n
  rfl

/-- Transporting an arity forth and back is definitionally harmless. -/
theorem castArity_symm
    {P G : Type u} {m n : ℕ}
    (h : m = n)
    (S : MajorizedCutSystem P G m) :
    castArity h.symm (castArity h S) = S := by
  subst n
  rfl

/-- The zero-stage nested parameter is the original parameter. -/
def csStageZeroEquiv
    (P G : Type u) :
    CSStageParam P G 0 ≃ P :=
  Equiv.refl P

/-- Expose the definitional successor equation of `CSStageParam` as an
equivalence so finite instances can be transported explicitly. -/
def csStageSuccNativeEquiv
    (P G : Type u) (r : ℕ) :
    CSStageParam P G (r + 1) ≃
      CSStageParam (P × (G × G)) G r :=
  Equiv.refl _

/-- Append one endpoint pair to the end of a decoded stage tuple. -/
def csAppendDecodedPairEquiv
    (P G : Type u) (r : ℕ) :
    ((P × (Fin r → G × G)) × (G × G)) ≃
      P × (Fin (r + 1) → G × G) where
  toFun q :=
    (q.1.1, Fin.snoc q.1.2 q.2)
  invFun q :=
    ((q.1, Fin.init q.2),
      q.2 (Fin.last r))
  left_inv q := by
    rcases q with ⟨⟨p, a⟩, last⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact
          @Fin.init_snoc r
            (fun _ => G × G) last a
    · exact
        @Fin.snoc_last r
          (fun _ => G × G) last a
  right_inv q := by
    rcases q with ⟨p, a⟩
    apply Prod.ext
    · rfl
    · exact Fin.snoc_init_self a

/-- Reassociate the parameter obtained by applying `next` after `r`
previous stages with the canonical `(r + 1)`-stage parameter. -/
def csStageDecodedAppendPairEquiv
    (P G : Type u) (r : ℕ) :
    (CSStageParam P G r × (G × G)) ≃
      CSStageParam P G (r + 1) :=
  (Equiv.prodCongr
      (csStageParamEquiv P G r)
      (Equiv.refl (G × G))).trans
    ((csAppendDecodedPairEquiv P G r).trans
      (csStageParamEquiv P G (r + 1)).symm)

/-- The same reassociation in the native nested representation.  Its
recursive definition makes compatibility with `iterNext` transparent. -/
def csStageAppendPairEquiv
    (P G : Type u) :
    ∀ r : ℕ,
      (CSStageParam P G r × (G × G)) ≃
        CSStageParam P G (r + 1)
  | 0 => Equiv.refl (P × (G × G))
  | r + 1 =>
      csStageAppendPairEquiv
        (P × (G × G)) G r

@[simp]
theorem csStageAppendPairEquiv_zero_apply
    (P G : Type u) (q : P × (G × G)) :
    csStageAppendPairEquiv P G 0 q = q := by
  rfl

theorem csStageAppendPairEquiv_succ
    (P G : Type u) (r : ℕ) :
    csStageAppendPairEquiv P G (r + 1) =
      csStageAppendPairEquiv
        (P × (G × G)) G r :=
  rfl

/-- The actual successor of an `r`-fold tower is the canonical
`(r + 1)`-fold tower after the explicit append-pair parameter
reassociation. -/
theorem iterNext_next_eq_iterNext_succ_reindex
    {P G : Type u} (n r : ℕ)
    (S : MajorizedCutSystem P G (n + (r + 1))) :
    (iterNext r
      (castArity
        (show n + (r + 1) = (n + 1) + r by omega)
        S)).next =
      (iterNext (r + 1) S).reindex
        (csStageAppendPairEquiv P G r) := by
  induction r generalizing P with
  | zero =>
      rfl
  | succ r ih =>
      have hcast :
          (castArity
            (show n + ((r + 1) + 1) =
                (n + 1) + (r + 1) by omega)
            S).next =
          castArity
            (show n + (r + 1) =
                (n + 1) + r by omega)
            S.next := by
        simpa only [] using
          castArity_next
            (show n + (r + 1) =
                (n + 1) + r by omega)
            S
      change
        (iterNext r
          (castArity
            (show n + ((r + 1) + 1) =
                (n + 1) + (r + 1) by omega)
            S).next).next =
          (iterNext (r + 1) S.next).reindex
            (csStageAppendPairEquiv
              (P × (G × G)) G r)
      rw [hcast]
      simpa only [] using
        ih (P := P × (G × G)) S.next

/-- The Boolean core product after one transform splits into the paid
head-majorant face and the two endpoint halves of the original core cube. -/
theorem terminalCoreProduct_next
    {P G : Type u} [Fintype P] [Fintype G]
    {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (a : Fin (n + 1) → G × G) :
    terminalCoreProduct S.next (p, a 0) (Fin.tail a) =
      (∏ bits : Fin n → Bool,
        S.majorant p 0
          (fun i =>
            selectPair (Fin.tail a i) (bits i))) *
        terminalCoreProduct S p a := by
  classical
  unfold terminalCoreProduct
  simp_rw [next_core_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  let F : Bool → (Fin n → Bool) → ℝ :=
    fun b bits =>
      S.core p
        (Fin.cons (selectPair (a 0) b)
          (fun i =>
            selectPair (Fin.tail a i) (bits i)))
  have hreindex :
      (∏ bits : Fin (n + 1) → Bool,
          S.core p
            (fun i => selectPair (a i) (bits i))) =
        ∏ q : Bool × (Fin n → Bool),
          F q.1 q.2 := by
    apply Fintype.prod_equiv
      (Fin.consEquiv
        (fun _ : Fin (n + 1) => Bool)).symm
    intro bits
    apply congrArg (S.core p)
    funext i
    refine Fin.cases ?_ (fun t => ?_) i
    · rfl
    · rfl
  rw [hreindex, Fintype.prod_prod_type,
    Fintype.prod_bool]
  simp [F]
  ring

/-- The symmetric terminal majorant product splits into the original head
face and the terminal majorant product of `next`. -/
theorem terminalMajorantProduct_eq_head_mul_next
    {P G : Type u} [Fintype P] [Fintype G] :
    ∀ {n : ℕ}
      (S : MajorizedCutSystem P G (n + 1))
      (p : P) (a : Fin (n + 1) → G × G),
      terminalMajorantProduct S p a =
        (∏ bits : Fin n → Bool,
          S.majorant p 0
            (fun i =>
              selectPair (Fin.tail a i) (bits i))) *
          terminalMajorantProduct S.next
            (p, a 0) (Fin.tail a) := by
  intro n
  cases n with
  | zero =>
      intro S p a
      rw [terminalMajorantProduct_succ,
        terminalMajorantProduct_zero, mul_one]
      rw [Fin.prod_univ_succ]
      simp only [Finset.univ_eq_empty,
        Finset.prod_empty, mul_one]
      apply Fintype.prod_congr
      intro bits
      apply congrArg (S.majorant p 0)
      funext q
      exact Fin.elim0 q
  | succ n =>
      intro S p a
      rw [terminalMajorantProduct_succ,
        terminalMajorantProduct_succ]
      rw [Fin.prod_univ_succ]
      apply congrArg₂ (· * ·)
      · apply Fintype.prod_congr
        intro bits
        apply congrArg (S.majorant p 0)
        funext q
        apply congrArg₂ selectPair
        · apply congrArg a
          apply Fin.ext
          rfl
        · rfl
      · apply Fintype.prod_congr
        intro i
        simp_rw [next_majorant_apply]
        rw [Finset.prod_mul_distrib]
        let F : Bool → (Fin n → Bool) → ℝ :=
          fun b bits =>
            S.majorant p i.succ
              (Fin.cons (selectPair (a 0) b)
                (eraseCoordinate i
                  (fun q =>
                    selectPair (Fin.tail a q)
                      (@Fin.insertNth n
                        (fun _ => Bool) i false bits q))))
        have hreindex :
            (∏ bits : Fin (n + 1) → Bool,
                S.majorant p i.succ
                  (eraseCoordinate i.succ
                    (fun q =>
                      selectPair (a q)
                        (@Fin.insertNth (n + 1)
                          (fun _ => Bool) i.succ
                            false bits q)))) =
              ∏ q : Bool × (Fin n → Bool),
                F q.1 q.2 := by
          apply Fintype.prod_equiv
            (Fin.consEquiv
              (fun _ : Fin (n + 1) => Bool)).symm
          intro bits
          apply congrArg (S.majorant p i.succ)
          have hinsert :
              (@Fin.insertNth (n + 1)
                (fun _ => Bool) i.succ false bits) =
                Fin.cons (bits 0)
                  (@Fin.insertNth n
                    (fun _ => Bool) i false
                      (Fin.tail bits)) := by
            rw [← Fin.cons_self_tail bits]
            exact Fin.insertNth_succ_cons
              i false (bits 0) (Fin.tail bits)
          rw [show
            (fun q =>
              selectPair (a q)
                (@Fin.insertNth (n + 1)
                  (fun _ => Bool) i.succ false
                    bits q)) =
              Fin.cons (selectPair (a 0) (bits 0))
                (fun q =>
                  selectPair (Fin.tail a q)
                    (@Fin.insertNth n
                      (fun _ => Bool) i false
                        (Fin.tail bits) q)) by
              rw [hinsert]
              funext q
              refine Fin.cases ?_ (fun t => ?_) q
              · rfl
              · rfl]
          exact eraseCoordinate_succ_cons i _ _
        rw [hreindex, Fintype.prod_prod_type,
          Fintype.prod_bool]
        simp [F, csConsInput]
        ring

/-- Closed terminal formula for repeated `next`: every Boolean copy of the
original core occurs once, and every designated majorant occurs once on
every vertex of its deleted-coordinate cube. -/
theorem iterNextTerminalDecoded_core
    {P G : Type u} [Fintype P] [Fintype G] :
    ∀ (n : ℕ) (S : MajorizedCutSystem P G n)
      (p : P) (a : Fin n → G × G),
      (iterNextTerminalDecoded S).core (p, a)
          (fun i => Fin.elim0 i) =
        terminalMajorantProduct S p a *
          terminalCoreProduct S p a := by
  intro n
  induction n generalizing P with
  | zero =>
      intro S p a
      simp [iterNextTerminalDecoded, iterNextTerminal,
        reindex, terminalMajorantProduct,
        terminalCoreProduct]
      apply congrArg (S.core p)
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro S p a
      change
        (iterNextTerminalDecoded S.next).core
            ((p, a 0), Fin.tail a)
            (fun i => Fin.elim0 i) =
          terminalMajorantProduct S p a *
            terminalCoreProduct S p a
      rw [ih S.next (p, a 0) (Fin.tail a)]
      rw [terminalCoreProduct_next,
        terminalMajorantProduct_eq_head_mul_next]
      ring

end MajorizedCutSystem

/-! ## The terminal AP cube and its face vertices -/

/-- A decoded terminal parameter is exactly a doubled AP cube: the base
pair occupies the distinguished coordinate and the remaining endpoint
pairs occupy its canonical `succAbove` complement. -/
def apCSTerminalCubeEquiv
    (n N : ℕ) (j : Fin (n + 1)) :
    ((Bool → ZMod N) ×
        (Fin n → ZMod N × ZMod N)) ≃
      CubePoint (n + 1) N where
  toFun q :=
    Fin.insertNth j q.1
      (fun t => selectPair (q.2 t))
  invFun x :=
    (x j,
      fun t =>
        (x (j.succAbove t) false,
          x (j.succAbove t) true))
  left_inv q := by
    rcases q with ⟨a, pairs⟩
    apply Prod.ext
    · funext b
      simp
    · funext t
      exact Prod.ext (by simp) (by simp)
  right_inv x := by
    apply (Fin.insertNth_eq_iff).2
    constructor
    · funext b
      simp
    · funext t b
      cases b <;> rfl

@[simp]
theorem apCSTerminalCubeEquiv_apply_distinguished
    (n N : ℕ) (j : Fin (n + 1))
    (p : (Bool → ZMod N) ×
      (Fin n → ZMod N × ZMod N))
    (b : Bool) :
    apCSTerminalCubeEquiv n N j p j b =
      p.1 b := by
  simp [apCSTerminalCubeEquiv]

@[simp]
theorem apCSTerminalCubeEquiv_apply_succAbove
    (n N : ℕ) (j : Fin (n + 1))
    (p : (Bool → ZMod N) ×
      (Fin n → ZMod N × ZMod N))
    (t : Fin n) (b : Bool) :
    apCSTerminalCubeEquiv n N j p
        (j.succAbove t) b =
      selectPair (p.2 t) b := by
  simp [apCSTerminalCubeEquiv]

/-- The vertex on face `j.succAbove t` encoded by a choice at `j` and
choices on all deleted coordinates other than `t`. -/
noncomputable def apCSTerminalFaceVertex
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (bits : Bool × (Fin m → Bool)) :
    DeletedCube ((m + 1) + 1) (j.succAbove t) :=
  fun q =>
    if hq : q.1 = j then
      bits.1
    else
      let d :=
        (finSuccAboveEquiv j).symm
          ⟨q.1, hq⟩
      have hjd : j.succAbove d = q.1 := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv j).apply_symm_apply
            ⟨q.1, hq⟩)
      have hdt : d ≠ t := by
        intro h
        apply q.2
        rw [← hjd, h]
      bits.2
        ((finSuccAboveEquiv t).symm
          ⟨d, hdt⟩)

/-- The preceding face-vertex encoding is a genuine equivalence, not only
a surjection used under a product. -/
noncomputable def apCSTerminalFaceVertexEquiv
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1)) :
    (Bool × (Fin m → Bool)) ≃
      DeletedCube ((m + 1) + 1)
        (j.succAbove t) where
  toFun := apCSTerminalFaceVertex m j t
  invFun ω :=
    (ω ⟨j, (Fin.succAbove_ne j t).symm⟩,
      fun r =>
        ω ⟨j.succAbove (t.succAbove r), by
          intro h
          exact (Fin.succAbove_ne t r)
            (Fin.succAbove_right_injective h)⟩)
  left_inv bits := by
    apply Prod.ext
    · simp [apCSTerminalFaceVertex]
    · funext r
      simp [apCSTerminalFaceVertex]
      apply congrArg bits.2
      apply (finSuccAboveEquiv t).injective
      rw [(finSuccAboveEquiv t).apply_symm_apply]
      apply Subtype.ext
      apply (finSuccAboveEquiv j).injective
      rw [(finSuccAboveEquiv j).apply_symm_apply]
      apply Subtype.ext
      rfl
  right_inv ω := by
    funext q
    by_cases hq : q.1 = j
    · have hqeq :
          q = ⟨j, (Fin.succAbove_ne j t).symm⟩ := by
        apply Subtype.ext
        exact hq
      rw [hqeq]
      simp [apCSTerminalFaceVertex]
    · let d :=
        (finSuccAboveEquiv j).symm
          ⟨q.1, hq⟩
      have hjd : j.succAbove d = q.1 := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv j).apply_symm_apply
            ⟨q.1, hq⟩)
      have hdt : d ≠ t := by
        intro h
        apply q.2
        rw [← hjd, h]
      let r :=
        (finSuccAboveEquiv t).symm
          ⟨d, hdt⟩
      have htr : t.succAbove r = d := by
        exact congrArg Subtype.val
          ((finSuccAboveEquiv t).apply_symm_apply
            ⟨d, hdt⟩)
      change
        (if h : q.1 = j then _ else _) = _
      rw [dif_neg hq]
      apply congrArg ω
      apply Subtype.ext
      change j.succAbove (t.succAbove r) = q.1
      rw [htr, hjd]

@[simp]
theorem apCSTerminalFaceVertex_distinguished
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (bits : Bool × (Fin m → Bool)) :
    apCSTerminalFaceVertex m j t bits
        ⟨j, (Fin.succAbove_ne j t).symm⟩ =
      bits.1 :=
  congrArg Prod.fst
    ((apCSTerminalFaceVertexEquiv
      m j t).left_inv bits)

@[simp]
theorem apCSTerminalFaceVertex_other
    (m : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (bits : Bool × (Fin m → Bool))
    (r : Fin m) :
    apCSTerminalFaceVertex m j t bits
        ⟨j.succAbove (t.succAbove r), by
          intro h
          exact (Fin.succAbove_ne t r)
            (Fin.succAbove_right_injective h)⟩ =
      bits.2 r :=
  congrFun
    (congrArg Prod.snd
      ((apCSTerminalFaceVertexEquiv
        m j t).left_inv bits)) r

/-- The AP simplex form reconstructed by a terminal majorant is the CFZ
linear form at the corresponding full terminal face vertex. -/
theorem apSimplexForm_eq_apLinearForm_terminalFaceVertex
    (m N : ℕ)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (p : Bool → ZMod N)
    (a : Fin (m + 1) → ZMod N × ZMod N)
    (b : Bool) (bits : Fin m → Bool) :
    apSimplexForm ((m + 1) + 1) N
        (j.succAbove t)
        (deleteCoordinate
          (Fin.insertNth j (p b)
            (fun q =>
              selectPair (a q)
                (@Fin.insertNth m
                  (fun _ => Bool) t false bits q)))
          (j.succAbove t)) =
      apLinearForm ((m + 1) + 1) N
        (j.succAbove t)
        (apCSTerminalFaceVertex
          m j t (b, bits))
        (apCSTerminalCubeEquiv
          (m + 1) N j (p, a)) := by
  unfold apSimplexForm apLinearForm
  apply Fintype.sum_congr
  intro q
  apply congrArg
    (fun z : ZMod N =>
      ((((q.1 : ℤ) -
        (j.succAbove t : ℤ) : ℤ) :
          ZMod N) * z))
  change
    (@Fin.insertNth (m + 1)
      (fun _ => ZMod N) j (p b)
      (fun q =>
        selectPair (a q)
          (@Fin.insertNth m
            (fun _ => Bool) t false bits q))) q.1 =
      apCSTerminalCubeEquiv
          (m + 1) N j (p, a) q.1
        (apCSTerminalFaceVertex
          m j t (b, bits) q)
  by_cases hq : q.1 = j
  · have hqeq :
        q = ⟨j, (Fin.succAbove_ne j t).symm⟩ := by
      apply Subtype.ext
      exact hq
    rw [hqeq]
    simp
  · let d :=
      (finSuccAboveEquiv j).symm
        ⟨q.1, hq⟩
    have hjd : j.succAbove d = q.1 := by
      exact congrArg Subtype.val
        ((finSuccAboveEquiv j).apply_symm_apply
          ⟨q.1, hq⟩)
    have hdt : d ≠ t := by
      intro h
      apply q.2
      rw [← hjd, h]
    let r :=
      (finSuccAboveEquiv t).symm
        ⟨d, hdt⟩
    have htr : t.succAbove r = d := by
      exact congrArg Subtype.val
        ((finSuccAboveEquiv t).apply_symm_apply
          ⟨d, hdt⟩)
    have hqeq :
        q =
          ⟨j.succAbove (t.succAbove r), by
            intro h
            exact (Fin.succAbove_ne t r)
              (Fin.succAbove_right_injective h)⟩ := by
      apply Subtype.ext
      change q.1 = j.succAbove (t.succAbove r)
      rw [htr, hjd]
    rw [hqeq]
    simp

/-- A fully doubled reconstructed majorant on one non-distinguished face
is exactly the full CFZ face product when that face is active, and one
when it is inactive. -/
theorem terminalFaceMajorantProduct_eq
    (m N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin ((m + 1) + 1) → Bool)
    (j : Fin ((m + 1) + 1))
    (t : Fin (m + 1))
    (p : Bool → ZMod N)
    (a : Fin (m + 1) → ZMod N × ZMod N) :
    (∏ bits : Fin m → Bool,
      apTwoCopyCutTest (m + 1) N
        (fun _ => apMaskedFaceMajorant ν active)
        j p t
        (eraseCoordinate t
          (fun q =>
            selectPair (a q)
              (@Fin.insertNth m
                (fun _ => Bool) t false bits q)))) =
      ∏ ω :
          DeletedCube ((m + 1) + 1)
            (j.succAbove t),
        if active (j.succAbove t) then
          ν (apLinearForm ((m + 1) + 1) N
            (j.succAbove t) ω
            (apCSTerminalCubeEquiv
              (m + 1) N j (p, a)))
        else 1 := by
  classical
  simp_rw [apTwoCopyCutTest_eraseCoordinate]
  cases hactive : active (j.succAbove t) with
  | false =>
      simp_rw [apMaskedFaceMajorant_of_inactive
        ν active (j.succAbove t) _ hactive]
      simp
  | true =>
      simp_rw [apMaskedFaceMajorant_of_active
        ν active (j.succAbove t) _ hactive]
      simp only [if_true]
      let F :
          Bool → (Fin m → Bool) → ℝ :=
        fun b bits =>
          ν (apSimplexForm ((m + 1) + 1) N
            (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (p b)
                (fun q =>
                  selectPair (a q)
                    (@Fin.insertNth m
                      (fun _ => Bool) t false bits q)))
              (j.succAbove t)))
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
      unfold F
      apply congrArg ν
      exact
        apSimplexForm_eq_apLinearForm_terminalFaceVertex
          m N j t p a bits.1 bits.2

namespace MajorizedCutSystem

/-- The Boolean copies of the concrete centered AP core are exactly the
centered product on the distinguished CFZ face. -/
theorem terminalCoreProduct_apTwoCopyMasked
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (p : Bool → ZMod N)
    (a : Fin n → ZMod N × ZMod N) :
    terminalCoreProduct
        (apTwoCopyMaskedMajorizedCutSystem
          n N ν active g j hrest) p a =
      faceCenteredProduct (n + 1) N ν j
        (apCSTerminalCubeEquiv n N j (p, a)) := by
  classical
  unfold terminalCoreProduct
  unfold apTwoCopyMaskedMajorizedCutSystem
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

/-- Every original concrete designated majorant contributes exactly the
active terminal exponent, face by face. -/
theorem terminalMajorantProduct_apTwoCopyMasked
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (p : Bool → ZMod N)
    (a : Fin n → ZMod N × ZMod N) :
    terminalMajorantProduct
        (apTwoCopyMaskedMajorizedCutSystem
          n N ν active g j hrest) p a =
      linearFormsProduct (n + 1) N ν
        (apCSActiveTerminalExponent active j)
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
              (fun _ =>
                apMaskedFaceMajorant ν active)
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
              apCSActiveTerminalExponent active j
                j ω
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
      rw [terminalFaceMajorantProduct_eq]
      apply Fintype.prod_congr
      intro ω
      simp [apCSActiveTerminalExponent,
        Fin.succAbove_ne]

/-- Pointwise terminal identity for the decoded concrete mixed system. -/
theorem iterNextTerminalDecoded_apTwoCopyMasked_core
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
    (p : Bool → ZMod N)
    (a : Fin n → ZMod N × ZMod N) :
    (iterNextTerminalDecoded
      (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest)).core
        (p, a) (fun i => Fin.elim0 i) =
      faceCenteredProduct (n + 1) N ν j
          (apCSTerminalCubeEquiv n N j (p, a)) *
        linearFormsProduct (n + 1) N ν
          (apCSActiveTerminalExponent active j)
          (apCSTerminalCubeEquiv
            n N j (p, a)) := by
  rw [iterNextTerminalDecoded_core]
  rw [terminalCoreProduct_apTwoCopyMasked,
    terminalMajorantProduct_apTwoCopyMasked]
  ring

/-- Decoding the terminal parameter does not change its zero-dimensional
form. -/
theorem iterNextTerminalDecoded_form
    {P G : Type u}
    [Fintype P] [Fintype G]
    {n : ℕ}
    (S : MajorizedCutSystem P G n) :
    (iterNextTerminalDecoded S).form =
      (iterNextTerminal n S).form :=
  reindex_form
    (iterNextTerminal n S)
    (csStageParamEquiv P G n).symm

/-- The complete terminal form is the weighted centered distinguished face
times precisely the active non-distinguished CFZ selector.  The statement
is uniform in the `Fintype` presentation of the nested parameter, which is
needed when it is reached through the actual recursive certificate. -/
theorem iterNextTerminal_apTwoCopyMasked_form_of_fintype
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j)
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
          (apTwoCopyMaskedMajorizedCutSystem
            n N ν active g j hrest)) =
      mean (fun x =>
        faceCenteredProduct (n + 1) N ν j x *
          linearFormsProduct (n + 1) N ν
            (apCSActiveTerminalExponent active j) x) := by
  letI : Fintype
      (CSStageParam
        (Bool → ZMod N) (ZMod N) n) :=
    stageFintype
  rw [← reindex_form
    (iterNextTerminal n
      (apTwoCopyMaskedMajorizedCutSystem
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
        (apTwoCopyMaskedMajorizedCutSystem
          n N ν active g j hrest)).core p x) = _
  rw [show
    (fun x : Fin 0 → ZMod N =>
      (iterNextTerminalDecoded
        (apTwoCopyMaskedMajorizedCutSystem
          n N ν active g j hrest)).core p x) =
      fun _ =>
        (iterNextTerminalDecoded
          (apTwoCopyMaskedMajorizedCutSystem
            n N ν active g j hrest)).core
          p (fun i => Fin.elim0 i) by
      funext x
      apply congrArg
      funext i
      exact Fin.elim0 i]
  rw [mean_const]
  exact
    iterNextTerminalDecoded_apTwoCopyMasked_core
      n N ν active g j hrest p.1 p.2

/-- Convenience specialization using the canonical decoded-stage finite
instance. -/
theorem iterNextTerminal_apTwoCopyMasked_form
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    (iterNextTerminal n
      (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest)).form =
      mean (fun x =>
        faceCenteredProduct (n + 1) N ν j x *
          linearFormsProduct (n + 1) N ν
            (apCSActiveTerminalExponent active j) x) :=
  iterNextTerminal_apTwoCopyMasked_form_of_fintype
    n N ν active g j hrest inferInstance

/-- A closed form for the fully iterated system supplies the terminal clause
at the end of the actual recursive `next` chain. -/
theorem hasCFZTerminal_of_iterNextTerminal_form
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k)
    {G : Type u} [instG : Fintype G] :
    ∀ {P : Type u} [Fintype P] {n : ℕ}
      (S : MajorizedCutSystem P G n)
      (other : LinearFormsExponent k),
      (∀ ω, other j ω = false) →
      (∀ stageFintype :
          Fintype (CSStageParam P G n),
        @form (CSStageParam P G n) G 0
            stageFintype instG
            (iterNextTerminal n S) =
          mean (fun x =>
            faceCenteredProduct k N ν j x *
              linearFormsProduct k N ν other x)) →
      HasCFZTerminal ν j S := by
  intro P instP n
  induction n generalizing P with
  | zero =>
      intro S other hother hform
      exact ⟨other, hother, hform instP⟩
  | succ n ih =>
      intro S other hother hform
      change HasCFZTerminal ν j S.next
      exact ih S.next other hother
        (fun stageFintype =>
          hform stageFintype)

/-- The concrete mixed AP system has the exact active-selector terminal
certificate, without any unit-majorant assumption. -/
theorem apTwoCopyMaskedMajorizedCutSystem_hasCFZTerminal
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    HasCFZTerminal ν j
      (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest) := by
  apply hasCFZTerminal_of_iterNextTerminal_form
    j
    (apTwoCopyMaskedMajorizedCutSystem
      n N ν active g j hrest)
    (apCSActiveTerminalExponent active j)
  · exact apCSActiveTerminalExponent_distinguished
      active j
  · intro stageFintype
    exact
      iterNextTerminal_apTwoCopyMasked_form_of_fintype
        n N ν active g j hrest stageFintype

/-- Terminal certificates, like full certificates, are invariant under a
finite reindexing of the external parameter. -/
theorem HasCFZTerminal.reindex
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k)
    {G : Type u} [Fintype G] :
    ∀ {P Q : Type u} [Fintype P] [Fintype Q]
      {n : ℕ}
      (S : MajorizedCutSystem P G n)
      (e : Q ≃ P),
      HasCFZTerminal ν j S →
        HasCFZTerminal ν j (S.reindex e) := by
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
      change HasCFZTerminal ν j S.next at hS
      change HasCFZTerminal ν j (S.reindex e).next
      rw [reindex_next]
      exact ih S.next
        (Equiv.prodCongr e
          (Equiv.refl (G × G)))
        hS

/-- A terminal certificate can be viewed from any intermediate point of
the native `iterNext` tower. -/
theorem HasCFZTerminal.iterNext
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (j : Fin k)
    {G : Type u} [Fintype G] :
    ∀ {P : Type u} [Fintype P]
      (r n : ℕ)
      (S : MajorizedCutSystem P G (n + r)),
      HasCFZTerminal ν j S →
        HasCFZTerminal ν j (iterNext r S) := by
  intro P instP r
  induction r generalizing P with
  | zero =>
      intro n S hS
      have hr :=
        hS.reindex j S
          (csStageZeroEquiv P G)
      simpa [csStageZeroEquiv,
        CSStageParam, iterNext] using hr
  | succ r ih =>
      intro n S hS
      change HasCFZTerminal ν j S.next at hS
      have htail :
          HasCFZTerminal ν j
            (MajorizedCutSystem.iterNext
              r S.next) :=
        ih n S.next hS
      have hr :=
        HasCFZTerminal.reindex j
          (MajorizedCutSystem.iterNext
            r S.next)
          (csStageSuccNativeEquiv P G r)
          htail
      simpa [csStageSuccNativeEquiv,
        CSStageParam, iterNext] using hr

/-- Every successor moment from `RelativeCountingDecoderStep`, together
with the terminal identity above, assembles into one structural CFZ
certificate for an arbitrary active mask.  The auxiliary equality `hk`
keeps the original AP arity fixed while the processed and live counts
change. -/
theorem apTwoCopyMasked_iterNext_hasCFZCertificate
    (k r s N : ℕ) [NeZero N]
    (hk : k = s + r)
    (ν : ZMod N → ℝ)
    (active : Fin (k + 1) → Bool)
    (g : Bool → APFaceWeightFamily k N)
    (j : Fin (k + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    HasCFZCertificate ν j
      (iterNext r
        (castArity hk
          (apTwoCopyMaskedMajorizedCutSystem
            k N ν active g j hrest))) := by
  induction s generalizing k r with
  | zero =>
      subst k
      have hterminal :=
        apTwoCopyMaskedMajorizedCutSystem_hasCFZTerminal
          (0 + r) N ν active g j hrest
      have hstage :=
        hterminal.iterNext j r 0
          (apTwoCopyMaskedMajorizedCutSystem
            (0 + r) N ν active g j hrest)
      change
        HasCFZTerminal ν j
          (iterNext r
            (apTwoCopyMaskedMajorizedCutSystem
              (0 + r) N ν active g j hrest))
      exact hstage
  | succ s ih =>
      subst k
      let S :=
        apTwoCopyMaskedMajorizedCutSystem
          ((s + 1) + r) N ν active g j hrest
      change
        HasCFZCertificate ν j
          (iterNext r S)
      refine
        ⟨apCSOrderedStageFaceExponent
            r s active j,
          ?_, ?_⟩
      · exact
          iterNext_apTwoCopyMasked_headMajorantMean
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

/-- Full mixed active-mask certificate for the original projected
two-copy system. -/
theorem apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    HasCFZCertificate ν j
      (apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest) := by
  have hstage :=
    apTwoCopyMasked_iterNext_hasCFZCertificate
      n 0 n N (by omega)
      ν active g j hrest
  have hreindexed :=
    hstage.reindex j
      (iterNext 0
        (castArity (show n = n + 0 by omega)
          (apTwoCopyMaskedMajorizedCutSystem
            n N ν active g j hrest)))
      (csStageZeroEquiv
        (Bool → ZMod N) (ZMod N)).symm
  change
    HasCFZCertificate ν j
      ((apTwoCopyMaskedMajorizedCutSystem
        n N ν active g j hrest).reindex
          (Equiv.refl (Bool → ZMod N))) at hreindexed
  rw [reindex_refl] at hreindexed
  exact hreindexed

end MajorizedCutSystem

/-! ## Quantitative active-mask endpoint -/

/-- Every active-mask projected two-copy correlation has the quantitative
CFZ root bound.  The recursive certificate is now internal: unlike
`abs_apTwoCopyCenteredCorrelation_le_of_masked_nextCertificate`, this
endpoint has no residual next-stage structural hypothesis. -/
theorem HasLinearFormsCondition.abs_apTwoCopyCenteredCorrelation_le_of_masked
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
      (MajorizedCutSystem.apTwoCopyMaskedMajorizedCutSystem_hasCFZCertificate
          (m + 1) N ν active g j hrest)
      hε hconvert

end Wikipedia.SzemeredisTheorem
