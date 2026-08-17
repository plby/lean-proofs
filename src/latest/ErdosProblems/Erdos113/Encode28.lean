import ErdosProblems.Erdos113.Conflict28
import ErdosProblems.Erdos113.WalkFin

open scoped Real SimpleGraph BigOperators

namespace Encode28

open Conflict28 WF

def cyclicAdd28 (i : Fin 28) (d : Nat) : Fin 28 :=
  ⟨(i.val + d) % 28, Nat.mod_lt _ (by omega)⟩

lemma cyclicAdd28_zero (i : Fin 28) : cyclicAdd28 i 0 = i := by
  apply Fin.ext
  simp [cyclicAdd28, Nat.mod_eq_of_lt i.isLt]

lemma cyclicAdd28_add (i : Fin 28) (a b : Nat) :
    cyclicAdd28 (cyclicAdd28 i a) b = cyclicAdd28 i (a + b) := by
  apply Fin.ext
  simp only [cyclicAdd28]
  omega

lemma cyclicAdd28_full (i : Fin 28) : cyclicAdd28 i 28 = i := by
  apply Fin.ext
  change (i.val + 28) % 28 = i.val
  omega

lemma exists_short_oriented_pair (i j : Fin 28) (hij : i ≠ j) :
    ∃ c : Fin 28, ∃ d : Fin 14,
      cyclicAdd28 c (d.val + 1) = j ∧ c = i ∨
      cyclicAdd28 c (d.val + 1) = i ∧ c = j := by
  by_cases hijv : i.val < j.val
  · let e := j.val - i.val
    by_cases he : e ≤ 14
    · refine ⟨i, ⟨e - 1, by dsimp [e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 28 - e
      refine ⟨j, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e', e]
      omega
  · have hjiv : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      omega
    let e := i.val - j.val
    by_cases he : e ≤ 14
    · refine ⟨j, ⟨e - 1, by dsimp [e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 28 - e
      refine ⟨i, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd28, e', e]
      omega


abbrev ClosedWalk28 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 28}

def cv {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (i : Fin 28) : W :=
  P.2.1.getVert i.val

lemma cv_adj_add_one {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (i : Fin 28) :
    A.Adj (cv P i) (cv P (cyclicAdd28 i 1)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 28
  · simpa [cv, cyclicAdd28, Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 27 := by omega
    have hend : P.2.1.getVert 28 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [cv, cyclicAdd28, hilast, hend, hstart] using hadj

def qSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 15) : W :=
  cv P (cyclicAdd28 c (r.val + 1))

lemma qSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 14) :
    A.Adj (qSeq P c r.castSucc) (qSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd28 c (r.val + 1))
  simpa only [qSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd28_add,
    show r.val + 1 + 1 = r.val + 2 by omega] using h

def qWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) :
    A.Walk (qSeq P c ⟨0, by omega⟩) (qSeq P c ⟨14, by omega⟩) :=
  walkOfFin 14 (qSeq P c) (qSeq_adj P c)

@[simp] lemma qWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) : (qWalk P c).length = 14 := by
  exact walkOfFin_length 14 (qSeq P c) (qSeq_adj P c)

lemma qWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (i : Nat) (hi : i ≤ 14) :
    (qWalk P c).getVert i = cv P (cyclicAdd28 c (i + 1)) := by
  simp only [qWalk]
  exact walkOfFin_getVert 14 (qSeq P c) (qSeq_adj P c) i hi

def pSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 14) : W :=
  cv P (cyclicAdd28 c (15 + r.val))

lemma pSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (r : Fin 13) :
    A.Adj (pSeq P c r.castSucc) (pSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd28 c (15 + r.val))
  simpa only [pSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd28_add,
    show 15 + r.val + 1 = 15 + (r.val + 1) by omega] using h

def pWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) :
    A.Walk (pSeq P c ⟨0, by omega⟩) (pSeq P c ⟨13, by omega⟩) :=
  walkOfFin 13 (pSeq P c) (pSeq_adj P c)

@[simp] lemma pWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) : (pWalk P c).length = 13 := by
  exact walkOfFin_length 13 (pSeq P c) (pSeq_adj P c)

lemma pWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk28 A) (c : Fin 28) (i : Nat) (hi : i ≤ 13) :
    (pWalk P c).getVert i = cv P (cyclicAdd28 c (15 + i)) := by
  simp only [pWalk]
  exact walkOfFin_getVert 13 (pSeq P c) (pSeq_adj P c) i hi

noncomputable def makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    BadHalfCycle A R := by
  let z := qSeq P c ⟨14, by omega⟩
  let x₁ := pSeq P c ⟨13, by omega⟩
  let p : FixedWalk A 13 z x₁ :=
    ⟨(pWalk P c).copy (by simp [z, qSeq, pSeq]) rfl, by
      rw [SimpleGraph.Walk.length_copy, pWalk_length]⟩
  let x₂ : A.neighborSet x₁ := ⟨qSeq P c ⟨0, by omega⟩, by
    have h := cv_adj_add_one P c
    simpa [x₁, qSeq, pSeq, cyclicAdd28_full] using h⟩
  let q : FixedWalk A 14 x₂.1 z := ⟨qWalk P c, qWalk_length P c⟩
  refine ⟨⟨z, x₁, p, x₂, q⟩, ?_⟩
  let i : Fin 7 := ⟨d.val / 2, by omega⟩
  let j : Fin 2 := ⟨d.val % 2, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, j, ?_⟩
  have hd : 2 * i.val + j.val = d.val := by
    dsimp [i, j]
    omega
  have hq := qWalk_getVert P c d.val (Nat.le_of_lt d.isLt)
  dsimp [x₁, q]
  rw [hd, hq]
  simpa [pSeq, cyclicAdd28_full] using hR

def cyclicOffset28 (c i : Fin 28) : Nat :=
  (i.val + 28 - c.val) % 28

lemma cyclicAdd_offset (c i : Fin 28) :
    cyclicAdd28 c (cyclicOffset28 c i) = i := by
  apply Fin.ext
  simp only [cyclicAdd28, cyclicOffset28]
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
    (c : Fin 28) (b : BadHalfCycle A R)
    (i : Fin 28) : W :=
  let d := cyclicOffset28 c i
  if d = 0 then b.1.2.1
  else if d ≤ 15 then packedWalkVertex (packedQ b) (d - 1)
  else packedWalkVertex (packedP b) (d - 15)

@[simp] lemma makeBadHalfCycle_x1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    (makeBadHalfCycle A R P c d hR).1.2.1 = pSeq P c ⟨13, by omega⟩ := by
  rfl

@[simp] lemma packedQ_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    packedQ (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨0, by omega⟩, qSeq P c ⟨14, by omega⟩, qWalk P c⟩ := by
  rfl

@[simp] lemma packedP_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) :
    packedP (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨14, by omega⟩, pSeq P c ⟨13, by omega⟩,
        (pWalk P c).copy (by simp [qSeq, pSeq]) rfl⟩ := by
  rfl

lemma packedP_makeBadHalfCycle_getVert {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1)))) (i : Nat) :
    packedWalkVertex (packedP (makeBadHalfCycle A R P c d hR)) i =
      (pWalk P c).getVert i := by
  unfold packedWalkVertex packedP
  dsimp [makeBadHalfCycle]
  simp only [SimpleGraph.Walk.getVert_copy]

lemma decode_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk28 A) (c : Fin 28) (d : Fin 14)
    (hR : R (cv P c) (cv P (cyclicAdd28 c (d.val + 1))))
    (i : Fin 28) :
    decodeHalfVertex c (makeBadHalfCycle A R P c d hR) i = cv P i := by
  let e := cyclicOffset28 c i
  have he_lt : e < 28 := Nat.mod_lt _ (by omega)
  by_cases he0 : e = 0
  · have hi : i = c := by
      have := cyclicAdd_offset c i
      symm
      simpa [e, he0, cyclicAdd28_zero] using this
    subst i
    simp [decodeHalfVertex, e, he0, pSeq,
      cyclicAdd28_full]
  · by_cases he29 : e ≤ 15
    · have hq := qWalk_getVert P c (e - 1) (by omega)
      have hadd : cyclicAdd28 c ((e - 1) + 1) = i := by
        rw [show e - 1 + 1 = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hq hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedQ_makeBadHalfCycle A R P c d hR]
      simp only [packedWalkVertex]
      rw [hq, hadd]
    · have hp := pWalk_getVert P c (e - 15) (by omega)
      have hadd : cyclicAdd28 c (15 + (e - 15)) = i := by
        rw [show 15 + (e - 15) = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he29 hp hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he29]
      rw [packedP_makeBadHalfCycle_getVert A R P c d hR, hp, hadd]

lemma closedWalk28_ext {W : Type*} {A : SimpleGraph W}
    (P Q : ClosedWalk28 A) (h : ∀ i, cv P i = cv Q i) : P = Q := by
  rcases P with ⟨x, p, hp⟩
  rcases Q with ⟨y, q, hq⟩
  have hxy : x = y := by
    have h0 := h ⟨0, by omega⟩
    simpa [cv] using h0
  subst y
  have hpq : p = q := by
    apply SimpleGraph.Walk.ext_getVert
    intro k
    by_cases hk : k < 28
    · simpa [cv] using h ⟨k, hk⟩
    · rw [p.getVert_of_length_le (by omega), q.getVert_of_length_le (by omega)]
  subst q
  rfl

abbrev BadClosedWalk28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {P : ClosedWalk28 A // ∃ i j, i ≠ j ∧ R (cv P i) (cv P j)}

lemma exists_orientedConflict28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk28 A R) :
    ∃ c : Fin 28, ∃ d : Fin 14,
      R (cv b.1 c) (cv b.1 (cyclicAdd28 c (d.val + 1))) := by
  rcases b.2 with ⟨i, j, hij, hR⟩
  rcases exists_short_oriented_pair i j hij with ⟨c, d, h | h⟩
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hR
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hsymm _ _ hR

noncomputable def orientedConflict28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk28 A R) :
    Σ c : Fin 28, {d : Fin 14 //
      R (cv b.1 c) (cv b.1 (cyclicAdd28 c (d.val + 1)))} := by
  let c := Classical.choose (exists_orientedConflict28 A R hsymm b)
  let d := Classical.choose (Classical.choose_spec
    (exists_orientedConflict28 A R hsymm b))
  exact ⟨c, d, Classical.choose_spec (Classical.choose_spec
    (exists_orientedConflict28 A R hsymm b))⟩

noncomputable def encodeBadClosedWalk28 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    BadClosedWalk28 A R → Fin 28 × BadHalfCycle A R := fun b ↦
  let w := orientedConflict28 A R hsymm b
  ⟨w.1, makeBadHalfCycle A R b.1 w.1 w.2.1 w.2.2⟩

lemma encodeBadClosedWalk28_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Function.Injective (encodeBadClosedWalk28 A R hsymm) := by
  intro b b' hbb'
  apply Subtype.ext
  apply closedWalk28_ext
  intro i
  have hdecode := congrArg (fun z : Fin 28 × BadHalfCycle A R ↦
    decodeHalfVertex z.1 z.2 i) hbb'
  simpa only [encodeBadClosedWalk28, decode_makeBadHalfCycle] using hdecode

lemma card_BadClosedWalk28_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Fintype.card (BadClosedWalk28 A R) ≤
      28 * Fintype.card (BadHalfCycle A R) := by
  calc
    Fintype.card (BadClosedWalk28 A R) ≤
        Fintype.card (Fin 28 × BadHalfCycle A R) :=
      Fintype.card_le_of_injective _ (encodeBadClosedWalk28_injective A R hsymm)
    _ = 28 * Fintype.card (BadHalfCycle A R) := by simp

lemma card_BadClosedWalk28_cast_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (t D s : ℝ) (ht : 0 < t) (hs : 0 ≤ s)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (BadClosedWalk28 A R) : ℝ) ≤
      28 * (D * t * (closedWalkCount A 26 : ℝ) +
        14 * s * t⁻¹ * (closedWalkCount A 28 : ℝ)) := by
  calc
    (Fintype.card (BadClosedWalk28 A R) : ℝ) ≤
        28 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast card_BadClosedWalk28_le A R hsymm
    _ ≤ 28 * (D * t * (closedWalkCount A 26 : ℝ) +
        14 * s * t⁻¹ * (closedWalkCount A 28 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (card_BadHalfCycle_le A R t D s ht hs hdegree hsymm hlocal) (by norm_num)

end Encode28


