import ErdosProblems.Erdos113.Consecutive56
import ErdosProblems.Erdos113.WalkFin

open scoped Real SimpleGraph BigOperators

namespace EncodeConsecutive56

open Consecutive56 WF

def cyclicAdd56 (i : Fin 56) (d : Nat) : Fin 56 :=
  ⟨(i.val + d) % 56, Nat.mod_lt _ (by omega)⟩

lemma cyclicAdd56_zero (i : Fin 56) : cyclicAdd56 i 0 = i := by
  apply Fin.ext
  simp [cyclicAdd56, Nat.mod_eq_of_lt i.isLt]

lemma cyclicAdd56_add (i : Fin 56) (a b : Nat) :
    cyclicAdd56 (cyclicAdd56 i a) b = cyclicAdd56 i (a + b) := by
  apply Fin.ext
  simp only [cyclicAdd56]
  omega

lemma cyclicAdd56_full (i : Fin 56) : cyclicAdd56 i 56 = i := by
  apply Fin.ext
  change (i.val + 56) % 56 = i.val
  omega

lemma exists_short_oriented_pair (i j : Fin 56) (hij : i ≠ j) :
    ∃ c : Fin 56, ∃ d : Fin 28,
      cyclicAdd56 c (d.val + 1) = j ∧ c = i ∨
      cyclicAdd56 c (d.val + 1) = i ∧ c = j := by
  by_cases hijv : i.val < j.val
  · let e := j.val - i.val
    by_cases he : e ≤ 28
    · refine ⟨i, ⟨e - 1, by dsimp [e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 56 - e
      refine ⟨j, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e', e]
      omega
  · have hjiv : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      omega
    let e := i.val - j.val
    by_cases he : e ≤ 28
    · refine ⟨j, ⟨e - 1, by dsimp [e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 56 - e
      refine ⟨i, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd56, e', e]
      omega


abbrev ClosedWalk56 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 56}

def cv {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (i : Fin 56) : W :=
  P.2.1.getVert i.val

lemma cv_adj_add_one {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (i : Fin 56) :
    A.Adj (cv P i) (cv P (cyclicAdd56 i 1)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 56
  · simpa [cv, cyclicAdd56, Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 55 := by omega
    have hend : P.2.1.getVert 56 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [cv, cyclicAdd56, hilast, hend, hstart] using hadj

def qSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 29) : W :=
  cv P (cyclicAdd56 c (r.val + 1))

lemma qSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 28) :
    A.Adj (qSeq P c r.castSucc) (qSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd56 c (r.val + 1))
  simpa only [qSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd56_add,
    show r.val + 1 + 1 = r.val + 2 by omega] using h

def qWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) :
    A.Walk (qSeq P c ⟨0, by omega⟩) (qSeq P c ⟨28, by omega⟩) :=
  walkOfFin 28 (qSeq P c) (qSeq_adj P c)

@[simp] lemma qWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) : (qWalk P c).length = 28 := by
  exact walkOfFin_length 28 (qSeq P c) (qSeq_adj P c)

lemma qWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (i : Nat) (hi : i ≤ 28) :
    (qWalk P c).getVert i = cv P (cyclicAdd56 c (i + 1)) := by
  simp only [qWalk]
  exact walkOfFin_getVert 28 (qSeq P c) (qSeq_adj P c) i hi

def pSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 28) : W :=
  cv P (cyclicAdd56 c (29 + r.val))

lemma pSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (r : Fin 27) :
    A.Adj (pSeq P c r.castSucc) (pSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd56 c (29 + r.val))
  simpa only [pSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd56_add,
    show 29 + r.val + 1 = 29 + (r.val + 1) by omega] using h

def pWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) :
    A.Walk (pSeq P c ⟨0, by omega⟩) (pSeq P c ⟨27, by omega⟩) :=
  walkOfFin 27 (pSeq P c) (pSeq_adj P c)

@[simp] lemma pWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) : (pWalk P c).length = 27 := by
  exact walkOfFin_length 27 (pSeq P c) (pSeq_adj P c)

lemma pWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk56 A) (c : Fin 56) (i : Nat) (hi : i ≤ 27) :
    (pWalk P c).getVert i = cv P (cyclicAdd56 c (29 + i)) := by
  simp only [pWalk]
  exact walkOfFin_getVert 27 (pSeq P c) (pSeq_adj P c) i hi

noncomputable def makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    BadHalfCycle A R := by
  let z := qSeq P c ⟨28, by omega⟩
  let x₁ := pSeq P c ⟨27, by omega⟩
  let p : FixedWalk A 27 z x₁ :=
    ⟨(pWalk P c).copy (by simp [z, qSeq, pSeq]) rfl, by
      rw [SimpleGraph.Walk.length_copy, pWalk_length]⟩
  let x₂ : A.neighborSet x₁ := ⟨qSeq P c ⟨0, by omega⟩, by
    have h := cv_adj_add_one P c
    simpa [x₁, qSeq, pSeq, cyclicAdd56_full] using h⟩
  let q : FixedWalk A 28 x₂.1 z := ⟨qWalk P c, qWalk_length P c⟩
  refine ⟨⟨z, x₁, p, x₂, q⟩, ?_⟩
  have hq := qWalk_getVert P c 1 (by omega)
  change R (pSeq P c ⟨27, by omega⟩) ((qWalk P c).getVert 1)
  rw [hq]
  simpa [pSeq, cyclicAdd56_full] using hR

def cyclicOffset56 (c i : Fin 56) : Nat :=
  (i.val + 56 - c.val) % 56

lemma cyclicAdd_offset (c i : Fin 56) :
    cyclicAdd56 c (cyclicOffset56 c i) = i := by
  apply Fin.ext
  simp only [cyclicAdd56, cyclicOffset56]
  omega

abbrev PackedWalk {W : Type*} (A : SimpleGraph W) :=
  Σ u : W, Σ v : W, A.Walk u v

def packedWalkVertex {W : Type*} {A : SimpleGraph W}
    (p : PackedWalk A) (i : Nat) : W := p.2.2.getVert i

def packedQ {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.2.2.2.1.1, b.1.1, b.1.2.2.2.2.1⟩

def packedP {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (b : BadHalfCycle A R) : PackedWalk A :=
  ⟨b.1.1, b.1.2.1, b.1.2.2.1.1⟩

def decodeHalfVertex {W : Type*} [Fintype W] [DecidableEq W]
    {A : SimpleGraph W} [DecidableRel A.Adj]
    {R : W → W → Prop} [DecidableRel R]
    (c : Fin 56) (b : BadHalfCycle A R)
    (i : Fin 56) : W :=
  let d := cyclicOffset56 c i
  if d = 0 then b.1.2.1
  else if d ≤ 29 then packedWalkVertex (packedQ b) (d - 1)
  else packedWalkVertex (packedP b) (d - 29)

@[simp] lemma makeBadHalfCycle_x1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    (makeBadHalfCycle A R P c d hR).1.2.1 = pSeq P c ⟨27, by omega⟩ := by
  rfl

@[simp] lemma packedQ_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    packedQ (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨0, by omega⟩, qSeq P c ⟨28, by omega⟩, qWalk P c⟩ := by
  rfl

@[simp] lemma packedP_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) :
    packedP (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨28, by omega⟩, pSeq P c ⟨27, by omega⟩,
        (pWalk P c).copy (by simp [qSeq, pSeq]) rfl⟩ := by
  rfl

lemma packedP_makeBadHalfCycle_getVert {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2))) (i : Nat) :
    packedWalkVertex (packedP (makeBadHalfCycle A R P c d hR)) i =
      (pWalk P c).getVert i := by
  unfold packedWalkVertex packedP
  dsimp [makeBadHalfCycle]
  simp only [SimpleGraph.Walk.getVert_copy]

lemma decode_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk56 A) (c : Fin 56) (d : Fin 28)
    (hR : R (cv P c) (cv P (cyclicAdd56 c 2)))
    (i : Fin 56) :
    decodeHalfVertex c (makeBadHalfCycle A R P c d hR) i = cv P i := by
  let e := cyclicOffset56 c i
  have he_lt : e < 56 := Nat.mod_lt _ (by omega)
  by_cases he0 : e = 0
  · have hi : i = c := by
      have := cyclicAdd_offset c i
      symm
      simpa [e, he0, cyclicAdd56_zero] using this
    subst i
    simp [decodeHalfVertex, e, he0, pSeq,
      cyclicAdd56_full]
  · by_cases he29 : e ≤ 29
    · have hq := qWalk_getVert P c (e - 1) (by omega)
      have hadd : cyclicAdd56 c ((e - 1) + 1) = i := by
        rw [show e - 1 + 1 = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hq hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedQ_makeBadHalfCycle A R P c d hR]
      simp only [packedWalkVertex]
      rw [hq, hadd]
    · have hp := pWalk_getVert P c (e - 29) (by omega)
      have hadd : cyclicAdd56 c (29 + (e - 29)) = i := by
        rw [show 29 + (e - 29) = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hp hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedP_makeBadHalfCycle_getVert A R P c d hR, hp, hadd]

lemma closedWalk56_ext {W : Type*} {A : SimpleGraph W}
    (P Q : ClosedWalk56 A) (h : ∀ i, cv P i = cv Q i) : P = Q := by
  rcases P with ⟨x, p, hp⟩
  rcases Q with ⟨y, q, hq⟩
  have hxy : x = y := by
    have h0 := h ⟨0, by omega⟩
    simpa [cv] using h0
  subst y
  have hpq : p = q := by
    apply SimpleGraph.Walk.ext_getVert
    intro k
    by_cases hk : k < 56
    · simpa [cv] using h ⟨k, hk⟩
    · rw [p.getVert_of_length_le (by omega), q.getVert_of_length_le (by omega)]
  subst q
  rfl

abbrev BadClosedWalk56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {P : ClosedWalk56 A // ∃ i, R (cv P i) (cv P (cyclicAdd56 i 2))}

lemma exists_orientedConflict56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk56 A R) :
    ∃ c : Fin 56, ∃ d : Fin 28,
      R (cv b.1 c) (cv b.1 (cyclicAdd56 c 2)) := by
  obtain ⟨c, hc⟩ := b.2
  exact ⟨c, 0, hc⟩

noncomputable def orientedConflict56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk56 A R) :
    Σ c : Fin 56, {d : Fin 28 //
      R (cv b.1 c) (cv b.1 (cyclicAdd56 c 2))} := by
  let c := Classical.choose (exists_orientedConflict56 A R hsymm b)
  let d := Classical.choose (Classical.choose_spec
    (exists_orientedConflict56 A R hsymm b))
  exact ⟨c, d, Classical.choose_spec (Classical.choose_spec
    (exists_orientedConflict56 A R hsymm b))⟩

noncomputable def encodeBadClosedWalk56 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    BadClosedWalk56 A R → Fin 56 × BadHalfCycle A R := fun b ↦
  let w := orientedConflict56 A R hsymm b
  ⟨w.1, makeBadHalfCycle A R b.1 w.1 w.2.1 w.2.2⟩

lemma encodeBadClosedWalk56_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Function.Injective (encodeBadClosedWalk56 A R hsymm) := by
  intro b b' hbb'
  apply Subtype.ext
  apply closedWalk56_ext
  intro i
  have hdecode := congrArg (fun z : Fin 56 × BadHalfCycle A R ↦
    decodeHalfVertex z.1 z.2 i) hbb'
  simpa only [encodeBadClosedWalk56, decode_makeBadHalfCycle] using hdecode

lemma card_BadClosedWalk56_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Fintype.card (BadClosedWalk56 A R) ≤
      56 * Fintype.card (BadHalfCycle A R) := by
  calc
    Fintype.card (BadClosedWalk56 A R) ≤
        Fintype.card (Fin 56 × BadHalfCycle A R) :=
      Fintype.card_le_of_injective _ (encodeBadClosedWalk56_injective A R hsymm)
    _ = 56 * Fintype.card (BadHalfCycle A R) := by simp

lemma card_BadClosedWalk56_cast_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (t D s : ℝ) (ht : 0 < t) (hs : 0 ≤ s)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y, A.Adj y u →
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (BadClosedWalk56 A R) : ℝ) ≤
      56 * (D * t * (closedWalkCount A 54 : ℝ) +
        s * t⁻¹ * (closedWalkCount A 56 : ℝ)) := by
  calc
    (Fintype.card (BadClosedWalk56 A R) : ℝ) ≤
        56 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast card_BadClosedWalk56_le A R hsymm
    _ ≤ 56 * (D * t * (closedWalkCount A 54 : ℝ) +
        s * t⁻¹ * (closedWalkCount A 56 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (card_BadHalfCycle_le A R t D s ht hs hdegree hsymm hlocal) (by norm_num)

end EncodeConsecutive56
