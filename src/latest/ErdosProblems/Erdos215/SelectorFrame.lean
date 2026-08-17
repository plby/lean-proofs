/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorLimit
import ErdosProblems.Erdos215.Global

/-! Transport the coordinate selector theorem to an arbitrary oriented frame. -/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos215

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace SelectorFrame

def pairToRatPoint (q : Selector.RatPoint) : RatPoint :=
  fun i ↦ if i = 0 then q.1 else q.2

def ratPointToPair (q : RatPoint) : Selector.RatPoint :=
  (q 0, q 1)

@[simp] lemma pairToRatPoint_apply_zero (q : Selector.RatPoint) :
    pairToRatPoint q 0 = q.1 := by simp [pairToRatPoint]

@[simp] lemma pairToRatPoint_apply_one (q : Selector.RatPoint) :
    pairToRatPoint q 1 = q.2 := by simp [pairToRatPoint]

@[simp] lemma pairToRatPoint_ratPointToPair (q : RatPoint) :
    pairToRatPoint (ratPointToPair q) = q := by
  funext i
  fin_cases i <;> simp [pairToRatPoint, ratPointToPair]

lemma pairToRatPoint_injective : Function.Injective pairToRatPoint := by
  intro q r h
  apply Prod.ext
  · exact congrArg (fun x : RatPoint ↦ x 0) h
  · exact congrArg (fun x : RatPoint ↦ x 1) h

def framePoint (L : OrientedFrame) (q : Selector.RatPoint) : Point :=
  L.fromCoords (ratPoint (pairToRatPoint q))

lemma framePoint_injective (L : OrientedFrame) : Function.Injective (framePoint L) := by
  intro q r h
  apply pairToRatPoint_injective
  apply ratPoint_injective
  exact L.fromCoords_injective h

lemma pairToRatPoint_liftedPoint (d : ℕ) (i j : Fin d) (k l : ℤ) :
    pairToRatPoint (Selector.liftedPoint d i j k l) =
      (fun r : Fin 2 ↦ if r = 0 then ((i : ℕ) : ℚ) / d + k
        else ((j : ℕ) : ℚ) / d + l) := by
  funext r
  fin_cases r <;> simp [pairToRatPoint, Selector.liftedPoint]

def coordinatePool (L : OrientedFrame) (P : Set Point) : Set Selector.RatPoint :=
  {q | framePoint L q ∈ P}

lemma coordinatePool_rich (L : OrientedFrame) (P : Set Point)
    (hP : Global.FrameRich L P) : Selector.Rich (coordinatePool L P) := by
  intro d hd i j a b
  let A : Set Selector.RatPoint := {q | ∃ k l : ℤ,
    q = Selector.liftedPoint d i j k l ∧
    a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ q ∈ coordinatePool L P}
  let B : Set Point := {x | ∃ k l : ℤ,
    x = L.fromCoords
      (ratPoint (fun r ↦ if r = 0 then (i : ℕ) / d + k else (j : ℕ) / d + l)) ∧
    a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ x ∈ P}
  have hB : B.Infinite := hP d hd i j a b
  have hsub : B ⊆ framePoint L '' A := by
    rintro x ⟨k, l, rfl, hk, hl, hp⟩
    let q := Selector.liftedPoint d i j k l
    refine ⟨q, ⟨k, l, rfl, hk, hl, ?_⟩, ?_⟩
    · change framePoint L q ∈ P
      simpa [framePoint, q, pairToRatPoint_liftedPoint] using hp
    · simp [framePoint, q, pairToRatPoint_liftedPoint]
  have himage : (framePoint L '' A).Infinite := hB.mono hsub
  have hA : A.Infinite := by
    by_contra hn
    exact (Set.not_infinite.mp hn).image (framePoint L) |>.not_infinite himage
  exact hA

lemma distSq_framePoint (L : OrientedFrame) (q r : Selector.RatPoint) :
    distSq (framePoint L q) (framePoint L r) = (Selector.sqDist q r : ℝ) := by
  rw [framePoint, framePoint, L.distSq_fromCoords]
  simp [distSq, Selector.sqDist, Fin.sum_univ_two, pairToRatPoint, ratPoint]

def frameSet (L : OrientedFrame) (T : Set Selector.RatPoint) : Set Point :=
  framePoint L '' T

lemma frameSet_subset (L : OrientedFrame) (P : Set Point)
    {T : Set Selector.RatPoint} (hT : T ⊆ coordinatePool L P) :
    frameSet L T ⊆ P := by
  rintro x ⟨q, hq, rfl⟩
  exact hT hq

lemma frameSet_partial (L : OrientedFrame) {T : Set Selector.RatPoint}
    (hT : Selector.IsPartial T) : IsPartialSteinhaus (frameSet L T) := by
  rintro p ⟨q, hq, rfl⟩ r ⟨s, hs, rfl⟩ hpq n hn
  have hqs : q ≠ s := fun h ↦ hpq (congrArg (framePoint L) h)
  have hnot := hT hq hs hqs
  apply hnot
  refine ⟨n, ?_⟩
  have hreal : (Selector.sqDist q s : ℝ) = (n : ℝ) := by
    rw [← distSq_framePoint L q s]
    exact hn
  exact_mod_cast hreal

lemma residue_eq_gives_int_translate {q r : Selector.RatPoint}
    (h : Selector.residue q = Selector.residue r) :
    ∃ z : IntPoint, pairToRatPoint q = pairToRatPoint r + fun i ↦ (z i : ℚ) := by
  have h₀ := congrArg Prod.fst h
  have h₁ := congrArg Prod.snd h
  have hm₀ := QuotientAddGroup.eq_iff_sub_mem.mp h₀
  have hm₁ := QuotientAddGroup.eq_iff_sub_mem.mp h₁
  rw [AddSubgroup.mem_zmultiples_iff] at hm₀ hm₁
  rcases hm₀ with ⟨z₀, hz₀⟩
  rcases hm₁ with ⟨z₁, hz₁⟩
  simp only [zsmul_eq_mul, mul_one] at hz₀ hz₁
  let z : IntPoint := fun i ↦ if i = 0 then z₀ else z₁
  refine ⟨z, ?_⟩
  funext i
  fin_cases i
  · simp [pairToRatPoint, z] at hz₀ ⊢
    rw [hz₀]
    ring
  · simp [pairToRatPoint, z] at hz₁ ⊢
    rw [hz₁]
    ring

lemma frameSet_hits (L : OrientedFrame) {T : Set Selector.RatPoint}
    (hT : Selector.HitsEveryIntegerTranslate T) :
    Global.HitsRationalTranslates (frameSet L T) L := by
  intro q
  obtain ⟨r, hrT, hr⟩ := hT (ratPointToPair q)
  obtain ⟨z, hz⟩ := residue_eq_gives_int_translate hr
  refine ⟨framePoint L r, ⟨⟨r, hrT, rfl⟩, ?_⟩⟩
  refine ⟨z, ?_⟩
  apply congrArg L.fromCoords
  ext i
  have hzi := congrFun hz i
  rw [pairToRatPoint_ratPointToPair] at hzi
  change (pairToRatPoint r i : ℝ) = (q i : ℝ) + (z i : ℝ)
  exact_mod_cast hzi

/-- The coordinate direct-limit theorem, transported to arbitrary oriented
frames. -/
theorem richSelectorTheorem_of_literalPrimeExtension :
    Selector.LiteralPrimeExtensionHypothesis → Global.RichSelectorTheorem := by
  intro hprime L P hP hrat w hw
  have hcoordRich : Selector.Rich (coordinatePool L P) := coordinatePool_rich L P hP
  cases w with
  | none =>
      obtain ⟨Tq, hTqP, hTqpartial, hTqhits, -⟩ :=
        Selector.rich_selector_of_literal_prime_extensions hprime
          (coordinatePool L P) hcoordRich none (by simp)
      refine ⟨frameSet L Tq, frameSet_subset L P hTqP,
        frameSet_partial L hTqpartial, frameSet_hits L hTqhits, ?_⟩
      intro x hx
      simp at hx
  | some w =>
      have hwP : w ∈ P := hw w rfl
      obtain ⟨q, hq⟩ := hrat w hwP
      let r : Selector.RatPoint := ratPointToPair q
      have hframe : framePoint L r = w := by
        dsimp only [r, framePoint]
        rw [pairToRatPoint_ratPointToPair]
        exact hq.symm
      have hrP : r ∈ coordinatePool L P := by
        change framePoint L r ∈ P
        rwa [hframe]
      have hopt : ∀ x, x ∈ (some r : Option Selector.RatPoint) →
          x ∈ coordinatePool L P := by
        intro x hx
        have hrx : r = x := by simpa using hx
        simpa [← hrx] using hrP
      obtain ⟨Tq, hTqP, hTqpartial, hTqhits, hTqr⟩ :=
        Selector.rich_selector_of_literal_prime_extensions hprime
          (coordinatePool L P) hcoordRich (some r) hopt
      have hrTq : r ∈ Tq := hTqr r (by simp)
      have hwT : w ∈ frameSet L Tq := by
        exact ⟨r, hrTq, hframe⟩
      refine ⟨frameSet L Tq, frameSet_subset L P hTqP,
        frameSet_partial L hTqpartial, frameSet_hits L hTqhits, ?_⟩
      intro x hx
      have hwx : w = x := Option.some.inj hx
      rwa [← hwx]

end SelectorFrame

end

end Erdos215
