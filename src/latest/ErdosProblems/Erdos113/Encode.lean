import ErdosProblems.Erdos113.Conflict
import ErdosProblems.Erdos113.WalkFin

open scoped Real SimpleGraph BigOperators

namespace Encode

open Conflict WF

def cyclicAdd1568 (i : Fin 1568) (d : Nat) : Fin 1568 :=
  ⟨(i.val + d) % 1568, Nat.mod_lt _ (by omega)⟩

lemma cyclicAdd1568_zero (i : Fin 1568) : cyclicAdd1568 i 0 = i := by
  apply Fin.ext
  simp [cyclicAdd1568, Nat.mod_eq_of_lt i.isLt]

lemma cyclicAdd1568_add (i : Fin 1568) (a b : Nat) :
    cyclicAdd1568 (cyclicAdd1568 i a) b = cyclicAdd1568 i (a + b) := by
  apply Fin.ext
  simp only [cyclicAdd1568]
  omega

lemma cyclicAdd1568_full (i : Fin 1568) : cyclicAdd1568 i 1568 = i := by
  apply Fin.ext
  change (i.val + 1568) % 1568 = i.val
  omega

lemma exists_short_oriented_pair (i j : Fin 1568) (hij : i ≠ j) :
    ∃ c : Fin 1568, ∃ d : Fin 784,
      cyclicAdd1568 c (d.val + 1) = j ∧ c = i ∨
      cyclicAdd1568 c (d.val + 1) = i ∧ c = j := by
  by_cases hijv : i.val < j.val
  · let e := j.val - i.val
    by_cases he : e ≤ 784
    · refine ⟨i, ⟨e - 1, by dsimp [e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 1568 - e
      refine ⟨j, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e', e]
      omega
  · have hjiv : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      omega
    let e := i.val - j.val
    by_cases he : e ≤ 784
    · refine ⟨j, ⟨e - 1, by dsimp [e]; omega⟩, Or.inr ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e]
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    · let e' := 1568 - e
      refine ⟨i, ⟨e' - 1, by dsimp [e', e]; omega⟩, Or.inl ⟨?_, rfl⟩⟩
      apply Fin.ext
      dsimp [cyclicAdd1568, e', e]
      omega


abbrev ClosedWalk1568 {W : Type*} (A : SimpleGraph W) :=
  Σ x : W, {p : A.Walk x x // p.length = 1568}

def cv {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) : W :=
  P.2.1.getVert i.val

lemma cv_adj_add_one {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (i : Fin 1568) :
    A.Adj (cv P i) (cv P (cyclicAdd1568 i 1)) := by
  have hi : i.val < P.2.1.length := by rw [P.2.2]; exact i.isLt
  have hadj := P.2.1.adj_getVert_succ hi
  by_cases hwrap : i.val + 1 < 1568
  · simpa [cv, cyclicAdd1568, Nat.mod_eq_of_lt hwrap] using hadj
  · have hilast : i.val = 1567 := by omega
    have hend : P.2.1.getVert 1568 = P.1 := by
      simpa only [P.2.2] using P.2.1.getVert_length
    have hstart : P.2.1.getVert 0 = P.1 := P.2.1.getVert_zero
    simpa [cv, cyclicAdd1568, hilast, hend, hstart] using hadj

def qSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 785) : W :=
  cv P (cyclicAdd1568 c (r.val + 1))

lemma qSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 784) :
    A.Adj (qSeq P c r.castSucc) (qSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd1568 c (r.val + 1))
  simpa only [qSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd1568_add,
    show r.val + 1 + 1 = r.val + 2 by omega] using h

def qWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) :
    A.Walk (qSeq P c ⟨0, by omega⟩) (qSeq P c ⟨784, by omega⟩) :=
  walkOfFin 784 (qSeq P c) (qSeq_adj P c)

@[simp] lemma qWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) : (qWalk P c).length = 784 := by
  exact walkOfFin_length 784 (qSeq P c) (qSeq_adj P c)

lemma qWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (i : Nat) (hi : i ≤ 784) :
    (qWalk P c).getVert i = cv P (cyclicAdd1568 c (i + 1)) := by
  simp only [qWalk]
  exact walkOfFin_getVert 784 (qSeq P c) (qSeq_adj P c) i hi

def pSeq {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 784) : W :=
  cv P (cyclicAdd1568 c (785 + r.val))

lemma pSeq_adj {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (r : Fin 783) :
    A.Adj (pSeq P c r.castSucc) (pSeq P c r.succ) := by
  have h := cv_adj_add_one P (cyclicAdd1568 c (785 + r.val))
  simpa only [pSeq, Fin.val_castSucc, Fin.val_succ, cyclicAdd1568_add,
    show 785 + r.val + 1 = 785 + (r.val + 1) by omega] using h

def pWalk {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) :
    A.Walk (pSeq P c ⟨0, by omega⟩) (pSeq P c ⟨783, by omega⟩) :=
  walkOfFin 783 (pSeq P c) (pSeq_adj P c)

@[simp] lemma pWalk_length {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) : (pWalk P c).length = 783 := by
  exact walkOfFin_length 783 (pSeq P c) (pSeq_adj P c)

lemma pWalk_getVert {W : Type*} {A : SimpleGraph W}
    (P : ClosedWalk1568 A) (c : Fin 1568) (i : Nat) (hi : i ≤ 783) :
    (pWalk P c).getVert i = cv P (cyclicAdd1568 c (785 + i)) := by
  simp only [pWalk]
  exact walkOfFin_getVert 783 (pSeq P c) (pSeq_adj P c) i hi

noncomputable def makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    BadHalfCycle A R := by
  let z := qSeq P c ⟨784, by omega⟩
  let x₁ := pSeq P c ⟨783, by omega⟩
  let p : FixedWalk A 783 z x₁ :=
    ⟨(pWalk P c).copy (by simp [z, qSeq, pSeq]) rfl, by
      rw [SimpleGraph.Walk.length_copy, pWalk_length]⟩
  let x₂ : A.neighborSet x₁ := ⟨qSeq P c ⟨0, by omega⟩, by
    have h := cv_adj_add_one P c
    simpa [x₁, qSeq, pSeq, cyclicAdd1568_full] using h⟩
  let q : FixedWalk A 784 x₂.1 z := ⟨qWalk P c, qWalk_length P c⟩
  refine ⟨⟨z, x₁, p, x₂, q⟩, ?_⟩
  let i : Fin 49 := ⟨d.val / 16, by omega⟩
  let j : Fin 16 := ⟨d.val % 16, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, j, ?_⟩
  have hd : 16 * i.val + j.val = d.val := by
    dsimp [i, j]
    omega
  have hq := qWalk_getVert P c d.val (Nat.le_of_lt d.isLt)
  dsimp [x₁, q]
  rw [hd, hq]
  simpa [pSeq, cyclicAdd1568_full] using hR

def cyclicOffset1568 (c i : Fin 1568) : Nat :=
  (i.val + 1568 - c.val) % 1568

lemma cyclicAdd_offset (c i : Fin 1568) :
    cyclicAdd1568 c (cyclicOffset1568 c i) = i := by
  apply Fin.ext
  simp only [cyclicAdd1568, cyclicOffset1568]
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
    (c : Fin 1568) (b : BadHalfCycle A R)
    (i : Fin 1568) : W :=
  let d := cyclicOffset1568 c i
  if d = 0 then b.1.2.1
  else if d ≤ 785 then packedWalkVertex (packedQ b) (d - 1)
  else packedWalkVertex (packedP b) (d - 785)

@[simp] lemma makeBadHalfCycle_x1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    (makeBadHalfCycle A R P c d hR).1.2.1 = pSeq P c ⟨783, by omega⟩ := by
  rfl

@[simp] lemma packedQ_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    packedQ (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨0, by omega⟩, qSeq P c ⟨784, by omega⟩, qWalk P c⟩ := by
  rfl

@[simp] lemma packedP_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) :
    packedP (makeBadHalfCycle A R P c d hR) =
      ⟨qSeq P c ⟨784, by omega⟩, pSeq P c ⟨783, by omega⟩,
        (pWalk P c).copy (by simp [qSeq, pSeq]) rfl⟩ := by
  rfl

lemma packedP_makeBadHalfCycle_getVert {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1)))) (i : Nat) :
    packedWalkVertex (packedP (makeBadHalfCycle A R P c d hR)) i =
      (pWalk P c).getVert i := by
  unfold packedWalkVertex packedP
  dsimp [makeBadHalfCycle]
  simp only [SimpleGraph.Walk.getVert_copy]

lemma decode_makeBadHalfCycle {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (P : ClosedWalk1568 A) (c : Fin 1568) (d : Fin 784)
    (hR : R (cv P c) (cv P (cyclicAdd1568 c (d.val + 1))))
    (i : Fin 1568) :
    decodeHalfVertex c (makeBadHalfCycle A R P c d hR) i = cv P i := by
  let e := cyclicOffset1568 c i
  have he_lt : e < 1568 := Nat.mod_lt _ (by omega)
  by_cases he0 : e = 0
  · have hi : i = c := by
      have := cyclicAdd_offset c i
      symm
      simpa [e, he0, cyclicAdd1568_zero] using this
    subst i
    simp [decodeHalfVertex, e, he0, pSeq,
      cyclicAdd1568_full]
  · by_cases he785 : e ≤ 785
    · have hq := qWalk_getVert P c (e - 1) (by omega)
      have hadd : cyclicAdd1568 c ((e - 1) + 1) = i := by
        rw [show e - 1 + 1 = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he785 hq hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he785]
      rw [packedQ_makeBadHalfCycle A R P c d hR]
      simp only [packedWalkVertex]
      rw [hq, hadd]
    · have hp := pWalk_getVert P c (e - 785) (by omega)
      have hadd : cyclicAdd1568 c (785 + (e - 785)) = i := by
        rw [show 785 + (e - 785) = e by omega]
        exact cyclicAdd_offset c i
      dsimp [e] at he0 he785 hp hadd ⊢
      simp only [decodeHalfVertex, he0, ↓reduceIte, he785]
      rw [packedP_makeBadHalfCycle_getVert A R P c d hR, hp, hadd]

lemma closedWalk1568_ext {W : Type*} {A : SimpleGraph W}
    (P Q : ClosedWalk1568 A) (h : ∀ i, cv P i = cv Q i) : P = Q := by
  rcases P with ⟨x, p, hp⟩
  rcases Q with ⟨y, q, hq⟩
  have hxy : x = y := by
    have h0 := h ⟨0, by omega⟩
    simpa [cv] using h0
  subst y
  have hpq : p = q := by
    apply SimpleGraph.Walk.ext_getVert
    intro k
    by_cases hk : k < 1568
    · simpa [cv] using h ⟨k, hk⟩
    · rw [p.getVert_of_length_le (by omega), q.getVert_of_length_le (by omega)]
  subst q
  rfl

abbrev BadClosedWalk1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R] :=
  {P : ClosedWalk1568 A // ∃ i j, i ≠ j ∧ R (cv P i) (cv P j)}

lemma exists_orientedConflict1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk1568 A R) :
    ∃ c : Fin 1568, ∃ d : Fin 784,
      R (cv b.1 c) (cv b.1 (cyclicAdd1568 c (d.val + 1))) := by
  rcases b.2 with ⟨i, j, hij, hR⟩
  rcases exists_short_oriented_pair i j hij with ⟨c, d, h | h⟩
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hR
  · refine ⟨c, d, ?_⟩
    rw [h.1, h.2]
    exact hsymm _ _ hR

noncomputable def orientedConflict1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) (b : BadClosedWalk1568 A R) :
    Σ c : Fin 1568, {d : Fin 784 //
      R (cv b.1 c) (cv b.1 (cyclicAdd1568 c (d.val + 1)))} := by
  let c := Classical.choose (exists_orientedConflict1568 A R hsymm b)
  let d := Classical.choose (Classical.choose_spec
    (exists_orientedConflict1568 A R hsymm b))
  exact ⟨c, d, Classical.choose_spec (Classical.choose_spec
    (exists_orientedConflict1568 A R hsymm b))⟩

noncomputable def encodeBadClosedWalk1568 {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    BadClosedWalk1568 A R → Fin 1568 × BadHalfCycle A R := fun b ↦
  let w := orientedConflict1568 A R hsymm b
  ⟨w.1, makeBadHalfCycle A R b.1 w.1 w.2.1 w.2.2⟩

lemma encodeBadClosedWalk1568_injective {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Function.Injective (encodeBadClosedWalk1568 A R hsymm) := by
  intro b b' hbb'
  apply Subtype.ext
  apply closedWalk1568_ext
  intro i
  have hdecode := congrArg (fun z : Fin 1568 × BadHalfCycle A R ↦
    decodeHalfVertex z.1 z.2 i) hbb'
  simpa only [encodeBadClosedWalk1568, decode_makeBadHalfCycle] using hdecode

lemma card_BadClosedWalk1568_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x) :
    Fintype.card (BadClosedWalk1568 A R) ≤
      1568 * Fintype.card (BadHalfCycle A R) := by
  calc
    Fintype.card (BadClosedWalk1568 A R) ≤
        Fintype.card (Fin 1568 × BadHalfCycle A R) :=
      Fintype.card_le_of_injective _ (encodeBadClosedWalk1568_injective A R hsymm)
    _ = 1568 * Fintype.card (BadHalfCycle A R) := by simp

lemma card_BadClosedWalk1568_cast_le {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (t D s : ℝ) (ht : 0 < t) (hs : 0 ≤ s)
    (hdegree : ∀ x, (A.degree x : ℝ) ≤ D)
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((A.neighborFinset y).filter (R u)).card : ℝ) ≤ s) :
    (Fintype.card (BadClosedWalk1568 A R) : ℝ) ≤
      1568 * (D * t * (closedWalkCount A 1566 : ℝ) +
        784 * s * t⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
  calc
    (Fintype.card (BadClosedWalk1568 A R) : ℝ) ≤
        1568 * (Fintype.card (BadHalfCycle A R) : ℝ) := by
      exact_mod_cast card_BadClosedWalk1568_le A R hsymm
    _ ≤ 1568 * (D * t * (closedWalkCount A 1566 : ℝ) +
        784 * s * t⁻¹ * (closedWalkCount A 1568 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (card_BadHalfCycle_le A R t D s ht hs hdegree hsymm hlocal) (by norm_num)

end Encode

