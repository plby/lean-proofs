/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos95.StoneTukey
import ErdosProblems.Erdos95.Algebraic
import ErdosProblems.Erdos95.SignCells
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.List.Sort
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A finite planar incidence bound

This file supplies the geometric input used in the converse for Erdős
Problem 606.  It specializes the already formalized finite Stone--Tukey
theorem to two variables and proves a deliberately non-sharp polynomial
partition estimate.  The exponent `69/100` is sufficient for the eventual
line-spectrum separation.
-/

open scoped BigOperators
open Finset

namespace Erdos606.PlanarIncidence

noncomputable section

abbrev Point := Fin 2 → ℝ
abbrev Poly2 := MvPolynomial (Fin 2) ℝ

/-! ## Two-variable Stone--Tukey cuts -/

abbrev CoeffIndex (k : ℕ) := Fin 2 → Fin (k + 1)

noncomputable def exponent {k : ℕ} (e : CoeffIndex k) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i : ℕ))

lemma exponent_injective {k : ℕ} : Function.Injective (@exponent k) := by
  intro e f h
  funext i
  apply Fin.ext
  have hi := congrArg (fun d : Fin 2 →₀ ℕ => d i) h
  simpa [exponent] using hi

noncomputable def boxMonomial {k : ℕ} (e : CoeffIndex k) : Poly2 :=
  MvPolynomial.monomial (exponent e) 1

lemma boxMonomial_linearIndependent (k : ℕ) :
    LinearIndependent ℝ (@boxMonomial k) := by
  change LinearIndependent ℝ
    (fun e : CoeffIndex k => MvPolynomial.monomial (exponent e) 1)
  exact (MvPolynomial.basisMonomials (Fin 2) ℝ).linearIndependent.comp
    (@exponent k) exponent_injective

noncomputable def polynomialOfCoefficients (k : ℕ) :
    (CoeffIndex k → ℝ) →ₗ[ℝ] Poly2 :=
  Fintype.linearCombination ℝ (@boxMonomial k)

lemma polynomialOfCoefficients_injective (k : ℕ) :
    Function.Injective (polynomialOfCoefficients k) :=
  (boxMonomial_linearIndependent k).fintypeLinearCombination_injective

lemma eval_polynomialOfCoefficients (k : ℕ)
    (c : CoeffIndex k → ℝ) (z : Point) :
    MvPolynomial.eval z (polynomialOfCoefficients k c) =
      ∑ e : CoeffIndex k, c e * MvPolynomial.eval z (boxMonomial e) := by
  rw [polynomialOfCoefficients, Fintype.linearCombination_apply]
  simp only [map_sum, MvPolynomial.smul_eval]

lemma totalDegree_boxMonomial_le (k : ℕ) (e : CoeffIndex k) :
    (boxMonomial e).totalDegree ≤ 2 * k := by
  rw [boxMonomial, MvPolynomial.totalDegree_monomial _ one_ne_zero]
  rw [Finsupp.sum_fintype (exponent e) (fun _ n => n) (fun _ => rfl)]
  calc
    ∑ i, exponent e i ≤ ∑ _i : Fin 2, k := by
      apply Finset.sum_le_sum
      intro i hi
      change (e i).val ≤ k
      omega
    _ = 2 * k := by simp

lemma totalDegree_polynomialOfCoefficients_le
    (k : ℕ) (c : CoeffIndex k → ℝ) :
    (polynomialOfCoefficients k c).totalDegree ≤ 2 * k := by
  rw [polynomialOfCoefficients, Fintype.linearCombination_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    (totalDegree_boxMonomial_le k e)

open Erdos95.Partitioning

/-- A nonzero two-variable polynomial simultaneously bisecting a finite
family of point sets. -/
lemma exists_bisecting_polynomial
    (k : ℕ) (I : Type) [Fintype I]
    (S : I → Finset Point) (hcard : Fintype.card I < (k + 1) ^ 2) :
    ∃ p : Poly2, p ≠ 0 ∧ p.totalDegree ≤ 2 * k ∧
      ∀ i, Bisects (fun x ↦ MvPolynomial.eval x p) (S i) := by
  classical
  have hdim : Fintype.card I < Fintype.card (CoeffIndex k) := by
    simpa [CoeffIndex] using hcard
  obtain ⟨c, hc, hbisect⟩ :=
    Erdos95.StoneTukey.finiteLinearBisection I (CoeffIndex k) Point hdim S
      (fun x e ↦ MvPolynomial.eval x (boxMonomial e))
  refine ⟨polynomialOfCoefficients k c, ?_,
    totalDegree_polynomialOfCoefficients_le k c, ?_⟩
  · intro hp
    apply hc
    apply polynomialOfCoefficients_injective k
    simpa using hp
  · intro i
    simpa only [eval_polynomialOfCoefficients] using hbisect i

/-! ## Strict sign cells -/

noncomputable def signCell (S : Finset Point) {j : ℕ}
    (p : Fin j → Poly2) (sign : Fin j → Bool) : Finset Point :=
  S.filter fun x ↦ ∀ i, if sign i then 0 < MvPolynomial.eval x (p i)
    else MvPolynomial.eval x (p i) < 0

@[simp] lemma mem_signCell_iff {S : Finset Point} {j : ℕ}
    {p : Fin j → Poly2} {sign : Fin j → Bool} {x : Point} :
    x ∈ signCell S p sign ↔ x ∈ S ∧
      ∀ i, if sign i then 0 < MvPolynomial.eval x (p i)
        else MvPolynomial.eval x (p i) < 0 := by
  classical
  simp [signCell]

lemma signCell_snoc (S : Finset Point) {j : ℕ}
    (p : Fin j → Poly2) (q : Poly2)
    (sign : Fin j → Bool) (b : Bool) :
    signCell S (Fin.snoc p q) (Fin.snoc sign b) =
      (signCell S p sign).filter fun x ↦
        if b then 0 < MvPolynomial.eval x q
        else MvPolynomial.eval x q < 0 := by
  classical
  ext x
  simp only [mem_signCell_iff, Finset.mem_filter]
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  tauto

lemma card_signCell_snoc_le_of_bisects
    (S : Finset Point) {j : ℕ} (p : Fin j → Poly2) (q : Poly2)
    (sign : Fin j → Bool)
    (hbisect : Bisects (fun x ↦ MvPolynomial.eval x q)
      (signCell S p sign)) (b : Bool) :
    2 * (signCell S (Fin.snoc p q) (Fin.snoc sign b)).card ≤
      (signCell S p sign).card := by
  rw [signCell_snoc]
  cases b with
  | false => simpa [Bisects] using hbisect.2
  | true => simpa [Bisects] using hbisect.1

/-- Iterated simultaneous bisection in the plane. -/
lemma exists_partition_cuts (S : Finset Point) (J : ℕ) (k : Fin J → ℕ)
    (hfit : ∀ j : Fin J, 2 ^ (j : ℕ) < (k j + 1) ^ 2) :
    ∃ p : Fin J → Poly2,
      (∀ j, p j ≠ 0 ∧ (p j).totalDegree ≤ 2 * k j) ∧
      ∀ sign : Fin J → Bool,
        2 ^ J * (signCell S p sign).card ≤ S.card := by
  classical
  induction J with
  | zero =>
      let p : Fin 0 → Poly2 := fun i ↦ Fin.elim0 i
      refine ⟨p, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · intro sign
        simp [signCell]
  | succ J ih =>
      have hfitInit : ∀ j : Fin J,
          2 ^ (j : ℕ) < (Fin.init k j + 1) ^ 2 := by
        intro j
        exact hfit j.castSucc
      obtain ⟨p, hp, hcells⟩ := ih (Fin.init k) hfitInit
      have hfitLast : 2 ^ J < (k (Fin.last J) + 1) ^ 2 := by
        simpa using hfit (Fin.last J)
      obtain ⟨q, hq, hqdeg, hqbisect⟩ :=
        exists_bisecting_polynomial (k (Fin.last J))
          (Fin J → Bool) (fun sign ↦ signCell S p sign) (by
            simpa using hfitLast)
      refine ⟨Fin.snoc p q, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · simpa using And.intro hq hqdeg
        · rw [Fin.snoc_castSucc]
          exact hp i
      · intro sign'
        rw [← Fin.snoc_init_self sign']
        calc
          2 ^ (J + 1) *
              (signCell S (Fin.snoc p q)
                (Fin.snoc (Fin.init sign') (sign' (Fin.last J)))).card =
              2 ^ J * (2 *
                (signCell S (Fin.snoc p q)
                  (Fin.snoc (Fin.init sign') (sign' (Fin.last J)))).card) := by
                rw [pow_succ]
                ring
          _ ≤ 2 ^ J * (signCell S p (Fin.init sign')).card :=
            Nat.mul_le_mul_left _
              (card_signCell_snoc_le_of_bisects S p q (Fin.init sign')
                (hqbisect (Fin.init sign')) (sign' (Fin.last J)))
          _ ≤ S.card := hcells (Fin.init sign')

noncomputable def partitionPolynomial {J : ℕ} (p : Fin J → Poly2) : Poly2 :=
  ∏ j, p j

lemma partitionPolynomial_ne_zero {J : ℕ} (p : Fin J → Poly2)
    (hp : ∀ j, p j ≠ 0) : partitionPolynomial p ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hp j

lemma partitionPolynomial_totalDegree_le {J : ℕ} (p : Fin J → Poly2)
    (k : Fin J → ℕ) (hp : ∀ j, (p j).totalDegree ≤ 2 * k j) :
    (partitionPolynomial p).totalDegree ≤ ∑ j, 2 * k j := by
  classical
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans
    (Finset.sum_le_sum fun j _ ↦ hp j)

/-! ## Lines and the sign cells they enter

We reuse the checked one-dimensional sign-pattern argument from Problem 95.
Every affine line in the plane is the first-two-coordinate projection of a
normalized Elekes--Sharir line, and a two-variable polynomial can be renamed
into three variables without changing any of its values on that projection.
-/

abbrev LineIndex := Point × Point
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable def linePoint (a b : Point) (t : ℝ) : Point :=
  fun i ↦ a i + t * (b i - a i)

lemma linePoint_zero (a b : Point) : linePoint a b 0 = a := by
  funext i
  simp [linePoint]

lemma linePoint_one (a b : Point) : linePoint a b 1 = b := by
  funext i
  simp [linePoint]

lemma linePoint_injective {a b : Point} (hab : a ≠ b) :
    Function.Injective (linePoint a b) := by
  intro s t hst
  by_contra hne
  apply hab
  funext i
  have hi := congrFun hst i
  dsimp [linePoint] at hi
  have hprod : (s - t) * (b i - a i) = 0 := by linarith
  have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hne
  exact sub_eq_zero.mp (mul_eq_zero.mp hprod |>.resolve_left hst0) |>.symm

def OnLine (a b x : Point) : Prop := ∃ t : ℝ, x = linePoint a b t

noncomputable def esLeft (a b : Point) : Erdos95.ES.PlanePoint :=
  WithLp.toLp 2 ![a 0 + (b 1 - a 1), a 1 - (b 0 - a 0)]

noncomputable def esRight (a b : Point) : Erdos95.ES.PlanePoint :=
  WithLp.toLp 2 ![a 0 - (b 1 - a 1), a 1 + (b 0 - a 0)]

lemma es_linePoint_first_two (a b : Point) (t : ℝ) (i : Fin 2) :
    Erdos95.ES.linePoint (esLeft a b) (esRight a b) t i.castSucc =
      linePoint a b t i := by
  fin_cases i <;> simp [Erdos95.ES.linePoint, esLeft, esRight, linePoint] <;> ring

noncomputable def liftPoly (q : Poly2) : Poly3 :=
  MvPolynomial.rename Fin.castSucc q

lemma eval_liftPoly (q : Poly2) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (liftPoly q) =
      MvPolynomial.eval (fun i : Fin 2 ↦ x i.castSucc) q := by
  simp [liftPoly, MvPolynomial.eval_rename, Function.comp_def]

lemma eval_liftPoly_esLine (q : Poly2) (a b : Point) (t : ℝ) :
    MvPolynomial.eval (Erdos95.ES.linePoint (esLeft a b) (esRight a b) t)
        (liftPoly q) =
      MvPolynomial.eval (linePoint a b t) q := by
  rw [eval_liftPoly]
  rw [show (fun i : Fin 2 ↦
      Erdos95.ES.linePoint (esLeft a b) (esRight a b) t i.castSucc) =
      linePoint a b t by
    funext i
    exact es_linePoint_first_two a b t i]

lemma lift_partitionPolynomial {J : ℕ} (p : Fin J → Poly2) :
    Erdos95.Partitioning.partitionPolynomial (fun j ↦ liftPoly (p j)) =
      liftPoly (partitionPolynomial p) := by
  classical
  simp [Erdos95.Partitioning.partitionPolynomial, partitionPolynomial,
    liftPoly, map_prod]

lemma totalDegree_lift_le (q : Poly2) :
    (liftPoly q).totalDegree ≤ q.totalDegree := by
  exact MvPolynomial.totalDegree_rename_le Fin.castSucc q

noncomputable def lineSignPatterns {J : ℕ} (p : Fin J → Poly2)
    (a b : Point) : Finset (Fin J → Bool) :=
  Erdos95.SignCells.lineSignPatterns (fun j ↦ liftPoly (p j))
    (esLeft a b) (esRight a b)

lemma mem_lineSignPatterns_iff {J : ℕ} {p : Fin J → Poly2}
    {a b : Point} {sign : Fin J → Bool} :
    sign ∈ lineSignPatterns p a b ↔ ∃ t : ℝ, ∀ j,
      if sign j then 0 < MvPolynomial.eval (linePoint a b t) (p j)
      else MvPolynomial.eval (linePoint a b t) (p j) < 0 := by
  rw [lineSignPatterns, Erdos95.SignCells.mem_lineSignPatterns_iff]
  constructor <;> rintro ⟨t, ht⟩ <;> refine ⟨t, fun j ↦ ?_⟩
  · simpa only [eval_liftPoly_esLine] using ht j
  · simpa only [eval_liftPoly_esLine] using ht j

lemma card_lineSignPatterns_le {J : ℕ} (p : Fin J → Poly2)
    (a b : Point) :
    (lineSignPatterns p a b).card ≤ (partitionPolynomial p).totalDegree + 1 := by
  classical
  by_cases hpat : (lineSignPatterns p a b).Nonempty
  · obtain ⟨sign, hsign⟩ := hpat
    have hsource :
        (lineSignPatterns p a b).card ≤
          (Erdos95.Partitioning.partitionPolynomial
            (fun j ↦ liftPoly (p j))).totalDegree + 1 := by
      exact Erdos95.SignCells.card_lineSignPatterns_le
        (fun j ↦ liftPoly (p j)) (esLeft a b) (esRight a b)
          (Erdos95.SignCells.lineRestriction_partitionPolynomial_ne_zero_of_mem_lineSignPatterns
            hsign)
    rw [lift_partitionPolynomial] at hsource
    exact hsource.trans (Nat.add_le_add_right
      (totalDegree_lift_le (partitionPolynomial p)) 1)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hpat]
    simp

noncomputable def cellLines (L : Finset LineIndex)
    (S : Finset Point) {J : ℕ} (p : Fin J → Poly2)
    (sign : Fin J → Bool) : Finset LineIndex := by
  classical
  exact L.filter fun l ↦ ∃ x ∈ signCell S p sign, OnLine l.1 l.2 x

lemma mem_cellLines_iff {L : Finset LineIndex} {S : Finset Point}
    {J : ℕ} {p : Fin J → Poly2} {sign : Fin J → Bool}
    {l : LineIndex} :
    l ∈ cellLines L S p sign ↔
      l ∈ L ∧ ∃ x ∈ signCell S p sign, OnLine l.1 l.2 x := by
  classical
  simp [cellLines]

lemma sign_mem_lineSignPatterns_of_mem_cellLines
    {L : Finset LineIndex} {S : Finset Point}
    {J : ℕ} {p : Fin J → Poly2} {sign : Fin J → Bool}
    {l : LineIndex} (hl : l ∈ cellLines L S p sign) :
    sign ∈ lineSignPatterns p l.1 l.2 := by
  obtain ⟨_hl, x, hx, t, rfl⟩ := mem_cellLines_iff.mp hl
  apply mem_lineSignPatterns_iff.mpr
  exact ⟨t, (mem_signCell_iff.mp hx).2⟩

noncomputable def cellLineIncidences (L : Finset LineIndex)
    (S : Finset Point) {J : ℕ} (p : Fin J → Poly2) :
    Finset (Σ _sign : (Fin J → Bool), LineIndex) :=
  (Finset.univ : Finset (Fin J → Bool)).sigma
    (fun sign ↦ cellLines L S p sign)

noncomputable def realizedLinePatterns (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly2) :
    Finset (Σ _l : LineIndex, (Fin J → Bool)) :=
  L.sigma fun l ↦ lineSignPatterns p l.1 l.2

lemma card_cellLineIncidences_le_realizedLinePatterns
    (L : Finset LineIndex) (S : Finset Point)
    {J : ℕ} (p : Fin J → Poly2) :
    (cellLineIncidences L S p).card ≤ (realizedLinePatterns L p).card := by
  classical
  let swap : (Σ _sign : (Fin J → Bool), LineIndex) →
      (Σ _l : LineIndex, (Fin J → Bool)) := fun z ↦ ⟨z.2, z.1⟩
  apply Finset.card_le_card_of_injOn swap
  · rintro ⟨sign, l⟩ hz
    change ⟨sign, l⟩ ∈ cellLineIncidences L S p at hz
    rw [cellLineIncidences, Finset.mem_sigma] at hz
    change ⟨l, sign⟩ ∈ realizedLinePatterns L p
    rw [realizedLinePatterns, Finset.mem_sigma]
    exact ⟨(mem_cellLines_iff.mp hz.2).1,
      sign_mem_lineSignPatterns_of_mem_cellLines hz.2⟩
  · rintro ⟨sign, l⟩ _ ⟨sign', l'⟩ _ h
    simp only [swap] at h
    injection h with hline hsign
    subst l'
    subst sign'
    rfl

lemma card_realizedLinePatterns_le (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly2) :
    (realizedLinePatterns L p).card ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  classical
  rw [realizedLinePatterns, Finset.card_sigma]
  calc
    (∑ l ∈ L, (lineSignPatterns p l.1 l.2).card) ≤
        ∑ _l ∈ L, ((partitionPolynomial p).totalDegree + 1) := by
      exact Finset.sum_le_sum fun l _ ↦ card_lineSignPatterns_le p l.1 l.2
    _ = L.card * ((partitionPolynomial p).totalDegree + 1) := by simp

lemma sum_card_cellLines_le (L : Finset LineIndex) (S : Finset Point)
    {J : ℕ} (p : Fin J → Poly2) :
    (∑ sign : Fin J → Bool, (cellLines L S p sign).card) ≤
      L.card * ((partitionPolynomial p).totalDegree + 1) := by
  rw [← Finset.card_sigma]
  change (cellLineIncidences L S p).card ≤ _
  exact (card_cellLineIncidences_le_realizedLinePatterns L S p).trans
    (card_realizedLinePatterns_le L p)

/-! ## Lines contained in a bivariate wall

The next finite transversal argument is a convenient form of the elementary
fact that a nonzero bivariate polynomial of degree `d` has at most `d`
distinct line components.  It avoids choosing normalized linear factors:
choose a line transverse to the finite family and avoiding every pairwise
intersection.  The intersections with the contained lines are then distinct
roots of one univariate restriction.
-/

noncomputable def lineSupport (l : LineIndex) : AffineSubspace ℝ Point :=
  affineSpan ℝ ({l.1, l.2} : Set Point)

lemma onLine_iff_mem_support {a b x : Point} :
    OnLine a b x ↔ x ∈ lineSupport (a, b) := by
  rw [lineSupport, mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    funext i
    simp [AffineMap.lineMap_apply, linePoint]
    ring
  · rintro ⟨t, ht⟩
    refine ⟨t, ht.symm.trans ?_⟩
    funext i
    simp [AffineMap.lineMap_apply, linePoint]
    ring

lemma lineSupport_eq_of_two_common {l m : LineIndex} {x y : Point}
    (hxl : OnLine l.1 l.2 x) (hyl : OnLine l.1 l.2 y)
    (hxm : OnLine m.1 m.2 x) (hym : OnLine m.1 m.2 y)
    (hxy : x ≠ y) : lineSupport l = lineSupport m := by
  have hl : affineSpan ℝ ({x, y} : Set Point) = lineSupport l :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (onLine_iff_mem_support.mp hxl) (onLine_iff_mem_support.mp hyl) hxy
  have hm : affineSpan ℝ ({x, y} : Set Point) = lineSupport m :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (onLine_iff_mem_support.mp hxm) (onLine_iff_mem_support.mp hym) hxy
  exact hl.symm.trans hm

def ValidLine (l : LineIndex) : Prop := l.1 ≠ l.2

def DistinctSupports (L : Finset LineIndex) : Prop :=
  Set.InjOn lineSupport L

noncomputable def direction (l : LineIndex) : Point :=
  fun i ↦ l.2 i - l.1 i

noncomputable def transverseDirection (c : ℝ) : Point := ![1, c]

noncomputable def cross (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

def ParallelSlope (l : LineIndex) (c : ℝ) : Prop :=
  cross (transverseDirection c) (direction l) = 0

lemma parallelSlope_unique {l : LineIndex} (hl : ValidLine l) :
    ∀ {c d : ℝ}, ParallelSlope l c → ParallelSlope l d → c = d := by
  intro c d hc hd
  have hcoord : direction l 0 ≠ 0 := by
    intro hzero
    have hy : direction l 1 = 0 := by
      dsimp [ParallelSlope, cross, transverseDirection] at hc
      simpa [hzero] using hc
    apply hl
    funext i
    fin_cases i
    · exact sub_eq_zero.mp hzero |>.symm
    · exact sub_eq_zero.mp hy |>.symm
  dsimp [ParallelSlope, cross, transverseDirection] at hc hd
  have : (c - d) * direction l 0 = 0 := by linarith
  exact sub_eq_zero.mp (mul_eq_zero.mp this |>.resolve_right hcoord)

noncomputable def intersectionParameter (z : Point) (l : LineIndex)
    (c : ℝ) : ℝ :=
  cross (fun i ↦ l.1 i - z i) (direction l) /
    cross (transverseDirection c) (direction l)

noncomputable def transversePoint (z : Point) (c t : ℝ) : Point :=
  fun i ↦ z i + t * transverseDirection c i

lemma transversePoint_injective_parameter (z : Point) (c : ℝ) :
    Function.Injective (transversePoint z c) := by
  intro s t h
  have h0 := congrFun h (0 : Fin 2)
  simpa [transversePoint, transverseDirection] using h0

lemma onLine_iff_cross_eq_zero {l : LineIndex} (hl : ValidLine l)
    (x : Point) :
    OnLine l.1 l.2 x ↔
      cross (fun i ↦ x i - l.1 i) (direction l) = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp [cross, linePoint, direction]
    ring
  · intro hcross
    by_cases hx : direction l 0 = 0
    · have hy : direction l 1 ≠ 0 := by
        intro hy
        apply hl
        funext i
        fin_cases i
        · exact sub_eq_zero.mp hx |>.symm
        · exact sub_eq_zero.mp hy |>.symm
      refine ⟨(x 1 - l.1 1) / direction l 1, ?_⟩
      funext i
      fin_cases i
      · dsimp [cross, direction] at hcross
        have hxpoint : x 0 = l.1 0 := by
          have : (x 0 - l.1 0) * direction l 1 = 0 := by
            dsimp [direction]
            rw [show l.2 0 - l.1 0 = 0 by simpa [direction] using hx,
              mul_zero, sub_zero] at hcross
            exact hcross
          exact sub_eq_zero.mp (mul_eq_zero.mp this |>.resolve_right hy)
        change x 0 = l.1 0 +
          ((x 1 - l.1 1) / direction l 1) * direction l 0
        rw [hxpoint, hx]
        ring
      · change x 1 = l.1 1 +
          ((x 1 - l.1 1) / direction l 1) * direction l 1
        field_simp [hy]
        ring
    · refine ⟨(x 0 - l.1 0) / direction l 0, ?_⟩
      funext i
      fin_cases i
      · change x 0 = l.1 0 +
          ((x 0 - l.1 0) / direction l 0) * direction l 0
        field_simp [hx]
        ring
      · dsimp [cross, direction] at hcross
        change x 1 = l.1 1 +
          ((x 0 - l.1 0) / direction l 0) * direction l 1
        have hc : (x 0 - l.1 0) * direction l 1 =
            (x 1 - l.1 1) * direction l 0 := by
          dsimp [direction]
          linarith
        field_simp [hx]
        nlinarith

lemma cross_transversePoint_sub (z : Point) (c t : ℝ) (l : LineIndex) :
    cross (fun i ↦ transversePoint z c t i - l.1 i) (direction l) =
      cross (fun i ↦ z i - l.1 i) (direction l) +
        t * cross (transverseDirection c) (direction l) := by
  simp [cross, transversePoint]
  ring

lemma cross_sub_rev (a z : Point) (v : Point) :
    cross (fun i ↦ a i - z i) v = -cross (fun i ↦ z i - a i) v := by
  simp [cross]
  ring

lemma intersectionPoint_onLine {z : Point} {l : LineIndex} {c : ℝ}
    (hnpar : ¬ ParallelSlope l c) :
    OnLine l.1 l.2
      (transversePoint z c (intersectionParameter z l c)) := by
  have hvalid : ValidLine l := by
    intro heq
    apply hnpar
    rcases l with ⟨a, b⟩
    simp only at heq
    subst b
    simp [ParallelSlope, cross, direction]
  apply (onLine_iff_cross_eq_zero hvalid _).mpr
  have hden : cross (transverseDirection c) (direction l) ≠ 0 := by
    simpa [ParallelSlope] using hnpar
  rw [cross_transversePoint_sub, cross_sub_rev]
  dsimp only [intersectionParameter]
  field_simp [hden]
  ring

def PairBad (z : Point) (l m : LineIndex) (c : ℝ) : Prop :=
  ¬ ParallelSlope l c ∧ ¬ ParallelSlope m c ∧
    intersectionParameter z l c = intersectionParameter z m c

lemma commonPoint_of_pairBad {z : Point} {l m : LineIndex} {c : ℝ}
    (h : PairBad z l m c) :
    OnLine l.1 l.2 (transversePoint z c (intersectionParameter z l c)) ∧
      OnLine m.1 m.2 (transversePoint z c (intersectionParameter z l c)) := by
  refine ⟨intersectionPoint_onLine h.1, ?_⟩
  rw [h.2.2]
  exact intersectionPoint_onLine h.2.1

lemma intersectionParameter_ne_zero_of_eval_ne_zero
    {q : Poly2} {z : Point} (hz : MvPolynomial.eval z q ≠ 0)
    {l : LineIndex} (hcontained : Erdos95.Algebraic.LineContained q l.1 (direction l))
    {c : ℝ} (hnpar : ¬ ParallelSlope l c) :
    intersectionParameter z l c ≠ 0 := by
  intro ht
  have hon := intersectionPoint_onLine (z := z) (l := l) hnpar
  have hpoint : transversePoint z c (intersectionParameter z l c) = z := by
    funext i
    simp [transversePoint, ht]
  rw [hpoint] at hon
  obtain ⟨t, htline⟩ := hon
  have hzero :=
    (Erdos95.Algebraic.lineContained_iff q l.1 (direction l)).mp hcontained t
  have hfun : (fun i ↦ l.1 i + t * direction l i) = linePoint l.1 l.2 t := by
    rfl
  rw [hfun, ← htline] at hzero
  exact hz hzero

lemma pairBad_unique_of_distinct_supports
    {q : Poly2} {z : Point} (hz : MvPolynomial.eval z q ≠ 0)
    {l m : LineIndex} (hlc : Erdos95.Algebraic.LineContained q l.1 (direction l))
    (hmc : Erdos95.Algebraic.LineContained q m.1 (direction m))
    (hne : lineSupport l ≠ lineSupport m) :
    ∀ {c d : ℝ}, PairBad z l m c → PairBad z l m d → c = d := by
  intro c d hc hd
  by_contra hcd
  let tc := intersectionParameter z l c
  let td := intersectionParameter z l d
  let xc := transversePoint z c tc
  let xd := transversePoint z d td
  have hcommonc := commonPoint_of_pairBad hc
  have hcommond := commonPoint_of_pairBad hd
  have htc0 : tc ≠ 0 :=
    intersectionParameter_ne_zero_of_eval_ne_zero hz hlc hc.1
  have hxdiff : xc ≠ xd := by
    intro heq
    have h0 := congrFun heq (0 : Fin 2)
    have htcTd : tc = td := by
      simpa [xc, xd, transversePoint, transverseDirection] using h0
    have h1 := congrFun heq (1 : Fin 2)
    dsimp [xc, xd, transversePoint, transverseDirection] at h1
    rw [htcTd] at h1
    have hmul : td * (c - d) = 0 := by
      calc
        td * (c - d) = (z 1 + td * c) - (z 1 + td * d) := by ring
        _ = 0 := sub_eq_zero.mpr h1
    rw [← htcTd] at hmul
    exact hcd (sub_eq_zero.mp (mul_eq_zero.mp hmul |>.resolve_left htc0))
  apply hne
  exact lineSupport_eq_of_two_common hcommonc.1 hcommond.1
    hcommonc.2 hcommond.2 hxdiff

lemma exists_eval_ne_zero {q : Poly2} (hq : q ≠ 0) :
    ∃ z : Point, MvPolynomial.eval z q ≠ 0 := by
  by_contra h
  push_neg at h
  apply hq
  apply MvPolynomial.funext
  intro z
  simpa using h z

noncomputable def representative (Q : ℝ → Prop) : ℝ := by
  classical
  exact if h : ∃ c, Q c then Classical.choose h else 0

lemma eq_representative_of_unique {Q : ℝ → Prop}
    (hunique : ∀ {c d}, Q c → Q d → c = d) {c : ℝ} (hc : Q c) :
    c = representative Q := by
  classical
  rw [representative, dif_pos ⟨c, hc⟩]
  exact hunique hc (Classical.choose_spec ⟨c, hc⟩)

noncomputable def forbiddenSlopes (z : Point) (L : Finset LineIndex) : Finset ℝ :=
  (L.image fun l ↦ representative (ParallelSlope l)) ∪
    ((L.product L).image fun lm ↦ representative (PairBad z lm.1 lm.2))

lemma exists_goodSlope (z : Point) (L : Finset LineIndex) :
    ∃ c : ℝ, c ∉ forbiddenSlopes z L := by
  exact Infinite.exists_notMem_finset (forbiddenSlopes z L)

lemma goodSlope_not_parallel {z : Point} {L : Finset LineIndex} {c : ℝ}
    (hc : c ∉ forbiddenSlopes z L) {l : LineIndex} (hlL : l ∈ L)
    (hl : ValidLine l) : ¬ ParallelSlope l c := by
  intro hpar
  have heq : c = representative (ParallelSlope l) :=
    eq_representative_of_unique (parallelSlope_unique hl) hpar
  apply hc
  rw [forbiddenSlopes, Finset.mem_union]
  exact Or.inl (Finset.mem_image.mpr ⟨l, hlL, heq.symm⟩)

lemma goodSlope_parameters_injective
    {q : Poly2} {z : Point} (hz : MvPolynomial.eval z q ≠ 0)
    {L : Finset LineIndex} (hvalid : ∀ l ∈ L, ValidLine l)
    (hcontained : ∀ l ∈ L,
      Erdos95.Algebraic.LineContained q l.1 (direction l))
    (hdistinct : DistinctSupports L) {c : ℝ}
    (hc : c ∉ forbiddenSlopes z L) :
    Set.InjOn (fun l ↦ intersectionParameter z l c) L := by
  intro l hlL m hmL heq
  by_contra hlm
  have hsupp : lineSupport l ≠ lineSupport m := by
    intro h
    exact hlm (hdistinct hlL hmL h)
  have hbad : PairBad z l m c := ⟨
    goodSlope_not_parallel hc hlL (hvalid l hlL),
    goodSlope_not_parallel hc hmL (hvalid m hmL), heq⟩
  have hrepr : c = representative (PairBad z l m) :=
    eq_representative_of_unique
      (pairBad_unique_of_distinct_supports hz
        (hcontained l hlL) (hcontained m hmL) hsupp) hbad
  apply hc
  rw [forbiddenSlopes, Finset.mem_union]
  have hlmprod : (l, m) ∈ L.product L :=
    Finset.mem_product.mpr ⟨hlL, hmL⟩
  exact Or.inr (Finset.mem_image.mpr ⟨(l, m), hlmprod, hrepr.symm⟩)

/-- A nonzero bivariate polynomial contains at most `totalDegree` distinct
valid affine lines. -/
lemma card_le_totalDegree_of_linesContained
    (q : Poly2) (hq : q ≠ 0) (L : Finset LineIndex)
    (hvalid : ∀ l ∈ L, ValidLine l)
    (hcontained : ∀ l ∈ L,
      Erdos95.Algebraic.LineContained q l.1 (direction l))
    (hdistinct : DistinctSupports L) :
    L.card ≤ q.totalDegree := by
  classical
  obtain ⟨z, hz⟩ := exists_eval_ne_zero hq
  obtain ⟨c, hc⟩ := exists_goodSlope z L
  let T : Finset ℝ := L.image fun l ↦ intersectionParameter z l c
  have hcardT : T.card = L.card := by
    change (L.image fun l ↦ intersectionParameter z l c).card = L.card
    rw [Finset.card_image_iff]
    exact goodSlope_parameters_injective hz hvalid hcontained hdistinct hc
  have hrestrict : Erdos95.Algebraic.lineRestriction q z (transverseDirection c) ≠ 0 := by
    intro hzero
    have heval := congrArg (fun f : Polynomial ℝ ↦ f.eval 0) hzero
    rw [Erdos95.Algebraic.eval_lineRestriction] at heval
    simp only [zero_mul, add_zero, Polynomial.eval_zero] at heval
    exact hz heval
  have hroots : ∀ t ∈ T,
      MvPolynomial.eval (fun i ↦ z i + t * transverseDirection c i) q = 0 := by
    intro t ht
    change t ∈ L.image (fun l ↦ intersectionParameter z l c) at ht
    rw [Finset.mem_image] at ht
    obtain ⟨l, hlL, rfl⟩ := ht
    have hnpar := goodSlope_not_parallel hc hlL (hvalid l hlL)
    obtain ⟨s, hs⟩ := intersectionPoint_onLine (z := z) (l := l) hnpar
    have hzero :=
      (Erdos95.Algebraic.lineContained_iff q l.1 (direction l)).mp
        (hcontained l hlL) s
    have hfun : (fun i ↦ l.1 i + s * direction l i) =
        linePoint l.1 l.2 s := rfl
    rw [hfun, ← hs] at hzero
    exact hzero
  rw [← hcardT]
  exact Erdos95.Algebraic.card_line_zeros_le_totalDegree q z
    (transverseDirection c) T hrestrict hroots

noncomputable def containedLines (q : Poly2) (L : Finset LineIndex) :
    Finset LineIndex := by
  classical
  exact L.filter fun l ↦ Erdos95.Algebraic.LineContained q l.1 (direction l)

@[simp] lemma mem_containedLines_iff {q : Poly2} {L : Finset LineIndex}
    {l : LineIndex} :
    l ∈ containedLines q L ↔
      l ∈ L ∧ Erdos95.Algebraic.LineContained q l.1 (direction l) := by
  classical
  simp [containedLines]

lemma card_containedLines_le_totalDegree
    (q : Poly2) (hq : q ≠ 0) (L : Finset LineIndex)
    (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L) :
    (containedLines q L).card ≤ q.totalDegree := by
  classical
  apply card_le_totalDegree_of_linesContained q hq (containedLines q L)
  · intro l hl
    exact hvalid l (mem_containedLines_iff.mp hl).1
  · intro l hl
    exact (mem_containedLines_iff.mp hl).2
  · intro l hl m hm h
    apply hdistinct
    · exact (mem_containedLines_iff.mp hl).1
    · exact (mem_containedLines_iff.mp hm).1
    · exact h

/-! ## Incidence bookkeeping -/

noncomputable def pointsOnLine (S : Finset Point) (l : LineIndex) : Finset Point := by
  classical
  exact S.filter fun x ↦ OnLine l.1 l.2 x

@[simp] lemma mem_pointsOnLine_iff {S : Finset Point} {l : LineIndex}
    {x : Point} :
    x ∈ pointsOnLine S l ↔ x ∈ S ∧ OnLine l.1 l.2 x := by
  classical
  simp [pointsOnLine]

lemma pointsOnLine_subset (S : Finset Point) (l : LineIndex) :
    pointsOnLine S l ⊆ S := by
  intro x hx
  exact (mem_pointsOnLine_iff.mp hx).1

noncomputable def incidenceCount (S : Finset Point) (L : Finset LineIndex) : ℕ :=
  ∑ l ∈ L, (pointsOnLine S l).card

lemma incidenceCount_mono_points {S T : Finset Point} (hST : S ⊆ T)
    (L : Finset LineIndex) : incidenceCount S L ≤ incidenceCount T L := by
  classical
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.card_le_card
  intro x hx
  exact mem_pointsOnLine_iff.mpr
    ⟨hST (mem_pointsOnLine_iff.mp hx).1, (mem_pointsOnLine_iff.mp hx).2⟩

lemma incidenceCount_mono_lines (S : Finset Point) {L M : Finset LineIndex}
    (hLM : L ⊆ M) : incidenceCount S L ≤ incidenceCount S M := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg hLM (fun _ _ _ ↦ Nat.zero_le _)

lemma incidenceCount_le_mul (S : Finset Point) (L : Finset LineIndex) :
    incidenceCount S L ≤ S.card * L.card := by
  classical
  calc
    incidenceCount S L ≤ ∑ _l ∈ L, S.card := by
      exact Finset.sum_le_sum fun l _ ↦
        Finset.card_le_card (pointsOnLine_subset S l)
    _ = S.card * L.card := by simp [mul_comm]

/-- The selected points covered by a finite family of lines. -/
noncomputable def coveredPoints (S : Finset Point) (L : Finset LineIndex) :
    Finset Point :=
  L.biUnion (pointsOnLine S)

lemma coveredPoints_subset (S : Finset Point) (L : Finset LineIndex) :
    coveredPoints S L ⊆ S := by
  classical
  intro x hx
  rw [coveredPoints, Finset.mem_biUnion] at hx
  obtain ⟨l, _hl, hxl⟩ := hx
  exact (mem_pointsOnLine_iff.mp hxl).1

lemma card_inter_pointsOnLine_le_one {S : Finset Point} {l m : LineIndex}
    (hne : lineSupport l ≠ lineSupport m) :
    (pointsOnLine S l ∩ pointsOnLine S m).card ≤ 1 := by
  classical
  by_contra h
  have htwo : 1 < (pointsOnLine S l ∩ pointsOnLine S m).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
  have hx' := Finset.mem_inter.mp hx
  have hy' := Finset.mem_inter.mp hy
  apply hne
  exact lineSupport_eq_of_two_common
    (mem_pointsOnLine_iff.mp hx'.1).2
    (mem_pointsOnLine_iff.mp hy'.1).2
    (mem_pointsOnLine_iff.mp hx'.2).2
    (mem_pointsOnLine_iff.mp hy'.2).2 hxy

lemma card_inter_coveredPoints_le {S : Finset Point} {l : LineIndex}
    {L : Finset LineIndex} (hl : l ∉ L)
    (hdistinct : DistinctSupports (insert l L)) :
    (pointsOnLine S l ∩ coveredPoints S L).card ≤ L.card := by
  classical
  have hset : pointsOnLine S l ∩ coveredPoints S L =
      L.biUnion (fun m ↦ pointsOnLine S l ∩ pointsOnLine S m) := by
    ext x
    simp only [coveredPoints, Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [hset]
  calc
    (L.biUnion (fun m ↦ pointsOnLine S l ∩ pointsOnLine S m)).card ≤
        ∑ m ∈ L, (pointsOnLine S l ∩ pointsOnLine S m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ L, 1 := by
      apply Finset.sum_le_sum
      intro m hm
      apply card_inter_pointsOnLine_le_one
      intro heq
      have hlm : l = m := hdistinct (by simp) (by simp [hm]) heq
      exact hl (by simpa [hlm] using hm)
    _ = L.card := by simp

/-- Incidences in a family of distinct planar lines exceed the size of their
union by at most the square of the number of lines. -/
lemma incidenceCount_le_covered_add_sq (S : Finset Point) (L : Finset LineIndex)
    (hdistinct : DistinctSupports L) :
    incidenceCount S L ≤ (coveredPoints S L).card + L.card ^ 2 := by
  classical
  induction L using Finset.induction_on with
  | empty => simp [incidenceCount, coveredPoints]
  | @insert l L hl ih =>
      have hdistL : DistinctSupports L := fun a ha b hb ↦
        hdistinct (by simp [ha]) (by simp [hb])
      have hi := ih hdistL
      have hinter := card_inter_coveredPoints_le (S := S) hl hdistinct
      have hunion := Finset.card_union_add_card_inter
        (pointsOnLine S l) (coveredPoints S L)
      have hcovered : coveredPoints S (insert l L) =
          pointsOnLine S l ∪ coveredPoints S L := by
        ext x
        simp [coveredPoints]
      rw [incidenceCount, Finset.sum_insert hl, ← incidenceCount]
      rw [hcovered]
      have hcard : (insert l L).card = L.card + 1 := by simp [hl]
      rw [hcard]
      have hsq : (L.card + 1) ^ 2 = L.card ^ 2 + 2 * L.card + 1 := by ring
      rw [hsq]
      omega

lemma incidenceCount_le_card_add_sq (S : Finset Point) (L : Finset LineIndex)
    (hdistinct : DistinctSupports L) :
    incidenceCount S L ≤ S.card + L.card ^ 2 := by
  exact (incidenceCount_le_covered_add_sq S L hdistinct).trans
    (Nat.add_le_add_right (Finset.card_le_card (coveredPoints_subset S L)) _)

noncomputable def parameterOf (l : LineIndex) (x : Point) : ℝ := by
  classical
  exact if h : OnLine l.1 l.2 x then Classical.choose h else 0

lemma linePoint_parameterOf {l : LineIndex} {x : Point}
    (hx : OnLine l.1 l.2 x) :
    x = linePoint l.1 l.2 (parameterOf l x) := by
  classical
  rw [parameterOf, dif_pos hx]
  exact Classical.choose_spec hx

lemma parameterOf_injective_on_line {l : LineIndex} (hl : ValidLine l) :
    Set.InjOn (parameterOf l) {x | OnLine l.1 l.2 x} := by
  intro x hx y hy hxy
  rw [linePoint_parameterOf hx, linePoint_parameterOf hy, hxy]

noncomputable def wallPoints (S : Finset Point) (q : Poly2) : Finset Point := by
  classical
  exact S.filter fun x ↦ MvPolynomial.eval x q = 0

@[simp] lemma mem_wallPoints_iff {S : Finset Point} {q : Poly2} {x : Point} :
    x ∈ wallPoints S q ↔ x ∈ S ∧ MvPolynomial.eval x q = 0 := by
  classical
  simp [wallPoints]

lemma card_pointsOnLine_wall_le_totalDegree
    (q : Poly2) (S : Finset Point) {l : LineIndex} (hl : ValidLine l)
    (hnot : ¬ Erdos95.Algebraic.LineContained q l.1 (direction l)) :
    (pointsOnLine (wallPoints S q) l).card ≤ q.totalDegree := by
  classical
  let T := pointsOnLine (wallPoints S q) l
  let U : Finset ℝ := T.image (parameterOf l)
  have hcardU : U.card = T.card := by
    change (T.image (parameterOf l)).card = T.card
    rw [Finset.card_image_iff]
    intro x hx y hy hxy
    apply parameterOf_injective_on_line hl
    · exact (mem_pointsOnLine_iff.mp hx).2
    · exact (mem_pointsOnLine_iff.mp hy).2
    · exact hxy
  have hroots : ∀ t ∈ U,
      MvPolynomial.eval (fun i ↦ l.1 i + t * direction l i) q = 0 := by
    intro t ht
    change t ∈ T.image (parameterOf l) at ht
    rw [Finset.mem_image] at ht
    obtain ⟨x, hxT, rfl⟩ := ht
    have hxline := (mem_pointsOnLine_iff.mp hxT).2
    have hxwall := (mem_wallPoints_iff.mp
      (mem_pointsOnLine_iff.mp hxT).1).2
    have hfun : (fun i ↦ l.1 i + parameterOf l x * direction l i) =
        linePoint l.1 l.2 (parameterOf l x) := rfl
    rw [hfun, ← linePoint_parameterOf hxline]
    exact hxwall
  rw [← hcardU]
  exact Erdos95.Algebraic.card_line_zeros_le_totalDegree q l.1
    (direction l) U hnot hroots

lemma incidenceCount_wall_le
    (q : Poly2) (hq : q ≠ 0) (S : Finset Point) (L : Finset LineIndex)
    (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L) :
    incidenceCount (wallPoints S q) L ≤
      q.totalDegree * ((wallPoints S q).card + L.card) := by
  classical
  let C := containedLines q L
  have hCcard : C.card ≤ q.totalDegree :=
    card_containedLines_le_totalDegree q hq L hvalid hdistinct
  rw [incidenceCount]
  rw [← Finset.sum_filter_add_sum_filter_not L
    (fun l ↦ Erdos95.Algebraic.LineContained q l.1 (direction l))
    (fun l ↦ (pointsOnLine (wallPoints S q) l).card)]
  calc
    (∑ l ∈ L.filter (fun l ↦
          Erdos95.Algebraic.LineContained q l.1 (direction l)),
        (pointsOnLine (wallPoints S q) l).card) +
        ∑ l ∈ L.filter (fun l ↦
          ¬ Erdos95.Algebraic.LineContained q l.1 (direction l)),
        (pointsOnLine (wallPoints S q) l).card ≤
      C.card * (wallPoints S q).card + L.card * q.totalDegree := by
        gcongr
        · calc
            (∑ l ∈ L.filter (fun l ↦
                Erdos95.Algebraic.LineContained q l.1 (direction l)),
              (pointsOnLine (wallPoints S q) l).card) ≤
                ∑ _l ∈ L.filter (fun l ↦
                  Erdos95.Algebraic.LineContained q l.1 (direction l)),
                    (wallPoints S q).card := by
                    apply Finset.sum_le_sum
                    intro l hl
                    exact Finset.card_le_card
                      (pointsOnLine_subset (wallPoints S q) l)
            _ = C.card * (wallPoints S q).card := by simp [C, containedLines]
        · calc
            (∑ l ∈ L.filter (fun l ↦
                ¬ Erdos95.Algebraic.LineContained q l.1 (direction l)),
              (pointsOnLine (wallPoints S q) l).card) ≤
                ∑ _l ∈ L.filter (fun l ↦
                  ¬ Erdos95.Algebraic.LineContained q l.1 (direction l)),
                  q.totalDegree := by
                    apply Finset.sum_le_sum
                    intro l hl
                    exact card_pointsOnLine_wall_le_totalDegree q S
                      (hvalid l (Finset.filter_subset _ _ hl))
                      (Finset.mem_filter.mp hl).2
            _ ≤ L.card * q.totalDegree := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              gcongr
              exact Finset.card_filter_le _ _
    _ ≤ q.totalDegree * ((wallPoints S q).card + L.card) := by
      nlinarith

noncomputable def strictPoints (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) : Finset Point :=
  (Finset.univ : Finset (Fin J → Bool)).biUnion fun sign ↦ signCell S p sign

lemma eval_partitionPolynomial (x : Point) {J : ℕ} (p : Fin J → Poly2) :
    MvPolynomial.eval x (partitionPolynomial p) =
      ∏ j, MvPolynomial.eval x (p j) := by
  classical
  simp [partitionPolynomial]

lemma subset_wall_union_strict (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) :
    S ⊆ wallPoints S (partitionPolynomial p) ∪ strictPoints S p := by
  classical
  intro x hxS
  by_cases hwall : MvPolynomial.eval x (partitionPolynomial p) = 0
  · exact Finset.mem_union_left _ (mem_wallPoints_iff.mpr ⟨hxS, hwall⟩)
  · apply Finset.mem_union_right
    rw [strictPoints, Finset.mem_biUnion]
    let sign : Fin J → Bool := fun j ↦ decide (0 < MvPolynomial.eval x (p j))
    refine ⟨sign, Finset.mem_univ _, mem_signCell_iff.mpr ⟨hxS, ?_⟩⟩
    intro j
    have hj : MvPolynomial.eval x (p j) ≠ 0 := by
      intro hz
      apply hwall
      rw [eval_partitionPolynomial]
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
    dsimp [sign]
    split
    · simpa using of_decide_eq_true ‹decide (0 < MvPolynomial.eval x (p j)) = true›
    · have hfalse : decide (0 < MvPolynomial.eval x (p j)) = false := by
        cases hdec : decide (0 < MvPolynomial.eval x (p j)) <;> simp_all
      have hnpos : ¬ 0 < MvPolynomial.eval x (p j) := by
        simpa using of_decide_eq_false
          hfalse
      exact lt_of_le_of_ne (le_of_not_gt hnpos) hj

lemma incidenceCount_union_le (S T : Finset Point) (L : Finset LineIndex) :
    incidenceCount (S ∪ T) L ≤ incidenceCount S L + incidenceCount T L := by
  classical
  rw [incidenceCount, incidenceCount, incidenceCount, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l hl
  have heq : pointsOnLine (S ∪ T) l =
      pointsOnLine S l ∪ pointsOnLine T l := by
    ext x
    simp only [mem_pointsOnLine_iff, Finset.mem_union]
    tauto
  rw [heq]
  exact Finset.card_union_le _ _

lemma incidenceCount_strictPoints_le (S : Finset Point) (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly2) :
    incidenceCount (strictPoints S p) L ≤
      ∑ sign : Fin J → Bool, incidenceCount (signCell S p sign) L := by
  classical
  rw [incidenceCount]
  calc
    (∑ l ∈ L, (pointsOnLine (strictPoints S p) l).card) ≤
        ∑ l ∈ L, ∑ sign : Fin J → Bool,
          (pointsOnLine (signCell S p sign) l).card := by
      apply Finset.sum_le_sum
      intro l hl
      have heq : pointsOnLine (strictPoints S p) l =
          (Finset.univ : Finset (Fin J → Bool)).biUnion fun sign ↦
            pointsOnLine (signCell S p sign) l := by
        change ((Finset.univ : Finset (Fin J → Bool)).biUnion
          (fun sign ↦ signCell S p sign)).filter
            (fun x ↦ OnLine l.1 l.2 x) = _
        rw [Finset.filter_biUnion]
        rfl
      rw [heq]
      simpa using (Finset.card_biUnion_le :
        ((Finset.univ : Finset (Fin J → Bool)).biUnion fun sign ↦
          pointsOnLine (signCell S p sign) l).card ≤ _)
    _ = ∑ sign : Fin J → Bool,
        incidenceCount (signCell S p sign) L := by
      simp only [incidenceCount]
      rw [Finset.sum_comm]

lemma incidenceCount_partition_le (S : Finset Point) (L : Finset LineIndex)
    {J : ℕ} (p : Fin J → Poly2) :
    incidenceCount S L ≤
      incidenceCount (wallPoints S (partitionPolynomial p)) L +
        ∑ sign : Fin J → Bool, incidenceCount (signCell S p sign) L := by
  calc
    incidenceCount S L ≤ incidenceCount
        (wallPoints S (partitionPolynomial p) ∪ strictPoints S p) L :=
      incidenceCount_mono_points (subset_wall_union_strict S p) L
    _ ≤ incidenceCount (wallPoints S (partitionPolynomial p)) L +
        incidenceCount (strictPoints S p) L := incidenceCount_union_le _ _ _
    _ ≤ _ := Nat.add_le_add_left (incidenceCount_strictPoints_le S L p) _

lemma signCells_pairwiseDisjoint (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) :
    ((Finset.univ : Finset (Fin J → Bool)) : Set (Fin J → Bool)).PairwiseDisjoint
      (signCell S p) := by
  classical
  intro sign₁ _ sign₂ _ hne
  change Disjoint (signCell S p sign₁) (signCell S p sign₂)
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have hsign : ∃ j, sign₁ j ≠ sign₂ j := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨j, hj⟩ := hsign
  have h₁ := (mem_signCell_iff.mp hx₁).2 j
  have h₂ := (mem_signCell_iff.mp hx₂).2 j
  cases hsj₁ : sign₁ j <;> cases hsj₂ : sign₂ j
  · exact hj (by simp [hsj₁, hsj₂])
  · have hneg : MvPolynomial.eval x (p j) < 0 := by simpa [hsj₁] using h₁
    have hpos : 0 < MvPolynomial.eval x (p j) := by simpa [hsj₂] using h₂
    linarith
  · have hpos : 0 < MvPolynomial.eval x (p j) := by simpa [hsj₁] using h₁
    have hneg : MvPolynomial.eval x (p j) < 0 := by simpa [hsj₂] using h₂
    linarith
  · exact hj (by simp [hsj₁, hsj₂])

lemma sum_card_signCell_le (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) :
    ∑ sign : Fin J → Bool, (signCell S p sign).card ≤ S.card := by
  classical
  rw [← Finset.card_biUnion (signCells_pairwiseDisjoint S p)]
  exact Finset.card_le_card fun x hx ↦ by
    rw [Finset.mem_biUnion] at hx
    obtain ⟨sign, _, hxs⟩ := hx
    exact (mem_signCell_iff.mp hxs).1

lemma wall_disjoint_strictPoints (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) :
    Disjoint (wallPoints S (partitionPolynomial p)) (strictPoints S p) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxw hxs
  have hzero := (mem_wallPoints_iff.mp hxw).2
  rw [strictPoints, Finset.mem_biUnion] at hxs
  obtain ⟨sign, _, hxcell⟩ := hxs
  have hnonzero : MvPolynomial.eval x (partitionPolynomial p) ≠ 0 := by
    rw [eval_partitionPolynomial]
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ by
      have hj := (mem_signCell_iff.mp hxcell).2 j
      split at hj <;> linarith
  exact hnonzero hzero

lemma wall_add_sum_cells_le (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) :
    (wallPoints S (partitionPolynomial p)).card +
      ∑ sign : Fin J → Bool, (signCell S p sign).card ≤ S.card := by
  classical
  rw [← Finset.card_biUnion (signCells_pairwiseDisjoint S p)]
  change (wallPoints S (partitionPolynomial p)).card +
      (strictPoints S p).card ≤ S.card
  rw [← Finset.card_union_of_disjoint (wall_disjoint_strictPoints S p)]
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_union.mp hx with hxw | hxs
  · exact (mem_wallPoints_iff.mp hxw).1
  · rw [strictPoints, Finset.mem_biUnion] at hxs
    obtain ⟨sign, _, hxcell⟩ := hxs
    exact (mem_signCell_iff.mp hxcell).1

noncomputable def richCellLines (L : Finset LineIndex) (S : Finset Point)
    {J : ℕ} (p : Fin J → Poly2) (sign : Fin J → Bool) : Finset LineIndex := by
  classical
  exact (cellLines L S p sign).filter fun l ↦
    2 ≤ (pointsOnLine (signCell S p sign) l).card

@[simp] lemma mem_richCellLines_iff {L : Finset LineIndex} {S : Finset Point}
    {J : ℕ} {p : Fin J → Poly2} {sign : Fin J → Bool} {l : LineIndex} :
    l ∈ richCellLines L S p sign ↔
      l ∈ L ∧ 2 ≤ (pointsOnLine (signCell S p sign) l).card := by
  classical
  constructor
  · intro hl
    have h := Finset.mem_filter.mp hl
    exact ⟨(mem_cellLines_iff.mp h.1).1, h.2⟩
  · rintro ⟨hlL, htwo⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, htwo⟩
    have hnonempty : (pointsOnLine (signCell S p sign) l).Nonempty := by
      exact Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hnonempty
    exact mem_cellLines_iff.mpr ⟨hlL, x,
      (mem_pointsOnLine_iff.mp hx).1, (mem_pointsOnLine_iff.mp hx).2⟩

lemma incidenceCount_cell_eq_cellLines
    (L : Finset LineIndex) (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) (sign : Fin J → Bool) :
    incidenceCount (signCell S p sign) L =
      incidenceCount (signCell S p sign) (cellLines L S p sign) := by
  classical
  rw [incidenceCount, incidenceCount]
  symm
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro l hlL hlnot
    have hnotcell : l ∉ cellLines L S p sign := hlnot
    have hempty : pointsOnLine (signCell S p sign) l = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      obtain ⟨x, hx⟩ := hne
      apply hnotcell
      exact mem_cellLines_iff.mpr ⟨hlL, x,
        (mem_pointsOnLine_iff.mp hx).1, (mem_pointsOnLine_iff.mp hx).2⟩
    simp [hempty]

lemma incidenceCount_cell_le_rich_add
    (L : Finset LineIndex) (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) (sign : Fin J → Bool) :
    incidenceCount (signCell S p sign) L ≤
      incidenceCount (signCell S p sign) (richCellLines L S p sign) +
        (cellLines L S p sign).card := by
  classical
  rw [incidenceCount_cell_eq_cellLines]
  rw [incidenceCount]
  rw [← Finset.sum_filter_add_sum_filter_not (cellLines L S p sign)
    (fun l ↦ 2 ≤ (pointsOnLine (signCell S p sign) l).card)
    (fun l ↦ (pointsOnLine (signCell S p sign) l).card)]
  change (∑ l ∈ richCellLines L S p sign,
      (pointsOnLine (signCell S p sign) l).card) +
      ∑ l ∈ (cellLines L S p sign).filter (fun l ↦
        ¬ 2 ≤ (pointsOnLine (signCell S p sign) l).card),
        (pointsOnLine (signCell S p sign) l).card ≤ _
  rw [← incidenceCount]
  gcongr
  calc
    (∑ l ∈ (cellLines L S p sign).filter (fun l ↦
        ¬ 2 ≤ (pointsOnLine (signCell S p sign) l).card),
      (pointsOnLine (signCell S p sign) l).card) ≤
        ∑ _l ∈ (cellLines L S p sign).filter (fun l ↦
          ¬ 2 ≤ (pointsOnLine (signCell S p sign) l).card), 1 := by
      apply Finset.sum_le_sum
      intro l hl
      have hn := (Finset.mem_filter.mp hl).2
      omega
    _ ≤ (cellLines L S p sign).card := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact Finset.card_filter_le _ _

lemma exists_richPair {T : Finset Point} {l : LineIndex}
    (h : 2 ≤ (pointsOnLine T l).card) :
    ∃ z : Point × Point, z.1 ∈ pointsOnLine T l ∧
      z.2 ∈ pointsOnLine T l ∧ z.1 ≠ z.2 := by
  have hone : 1 < (pointsOnLine T l).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (Finset.one_lt_card (s := pointsOnLine T l)).mp hone
  exact ⟨(x, y), hx, hy, hxy⟩

noncomputable def richPair (T : Finset Point) (l : LineIndex) : Point × Point := by
  classical
  exact if h : 2 ≤ (pointsOnLine T l).card then
    Classical.choose (exists_richPair h)
  else (0, 0)

lemma richPair_spec {T : Finset Point} {l : LineIndex}
    (h : 2 ≤ (pointsOnLine T l).card) :
    (richPair T l).1 ∈ pointsOnLine T l ∧
      (richPair T l).2 ∈ pointsOnLine T l ∧
      (richPair T l).1 ≠ (richPair T l).2 := by
  classical
  rw [richPair, dif_pos h]
  exact Classical.choose_spec (exists_richPair h)

lemma card_richCellLines_le_sq
    (L : Finset LineIndex) (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) (sign : Fin J → Bool)
    (hdistinct : DistinctSupports L) :
    (richCellLines L S p sign).card ≤ (signCell S p sign).card ^ 2 := by
  classical
  let B := richCellLines L S p sign
  let T := signCell S p sign
  have hmaps : Set.MapsTo (richPair T) B (T.product T) := by
    intro l hl
    have hmem := mem_richCellLines_iff.mp hl
    have hs := richPair_spec hmem.2
    exact Finset.mem_product.mpr
      ⟨(mem_pointsOnLine_iff.mp hs.1).1,
        (mem_pointsOnLine_iff.mp hs.2.1).1⟩
  have hinj : Set.InjOn (richPair T) B := by
    intro l hl m hm heq
    have hlm := mem_richCellLines_iff.mp hl
    have hmm := mem_richCellLines_iff.mp hm
    have hsl := richPair_spec hlm.2
    have hsm := richPair_spec hmm.2
    have hp1 : (richPair T l).1 = (richPair T m).1 := congrArg Prod.fst heq
    have hp2 : (richPair T l).2 = (richPair T m).2 := congrArg Prod.snd heq
    apply hdistinct hlm.1 hmm.1
    exact lineSupport_eq_of_two_common
      (mem_pointsOnLine_iff.mp hsl.1).2
      (mem_pointsOnLine_iff.mp hsl.2.1).2
      (hp1 ▸ (mem_pointsOnLine_iff.mp hsm.1).2)
      (hp2 ▸ (mem_pointsOnLine_iff.mp hsm.2.1).2)
      hsl.2.2
  calc
    B.card ≤ (T.product T).card := Finset.card_le_card_of_injOn
      (richPair T) hmaps hinj
    _ = T.card ^ 2 := by simp [pow_two]

lemma sum_card_cellLines_le_degree
    (L : Finset LineIndex) (S : Finset Point) {J : ℕ}
    (p : Fin J → Poly2) {D : ℕ}
    (hdeg : (partitionPolynomial p).totalDegree ≤ D) :
    ∑ sign : Fin J → Bool, (cellLines L S p sign).card ≤
      (D + 1) * L.card := by
  calc
    _ ≤ L.card * ((partitionPolynomial p).totalDegree + 1) :=
      sum_card_cellLines_le L S p
    _ ≤ L.card * (D + 1) := by gcongr
    _ = (D + 1) * L.card := by ring

/-! ## The fixed real-power contraction -/

lemma sum_rpow_le_card_factor {ι : Type} (s : Finset ι) (x : ι → ℝ)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hs : s.Nonempty) :
    ∑ i ∈ s, (x i) ^ a ≤
      (s.card : ℝ) ^ (1 - a) * (∑ i ∈ s, x i) ^ a := by
  let N : ℝ := s.card
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Finset.card_pos.mpr hs
  let w : ι → ℝ := fun _ ↦ 1 / N
  have hw0 : ∀ i ∈ s, 0 ≤ w i := by
    intro i hi
    positivity
  have hwsum : ∑ i ∈ s, w i = 1 := by
    simp [w, N, hNpos.ne']
  have hJ : ∑ i ∈ s, w i * (x i) ^ a ≤
      (∑ i ∈ s, w i * x i) ^ a := by
    simpa only [smul_eq_mul] using
      (Real.concaveOn_rpow ha0 ha1).le_map_sum
        (t := s) (w := w) (p := x) hw0 hwsum
        (fun i hi ↦ hx i hi)
  have hleft : (∑ i ∈ s, w i * (x i) ^ a) =
      (1 / N) * ∑ i ∈ s, (x i) ^ a := by
    simp only [w]
    rw [Finset.mul_sum]
  have hright : (∑ i ∈ s, w i * x i) ^ a =
      (1 / N) ^ a * (∑ i ∈ s, x i) ^ a := by
    simp only [w]
    have hsumx : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi ↦ hx i hi
    rw [← Finset.mul_sum, Real.mul_rpow (by positivity) hsumx]
  rw [hleft, hright] at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ hNpos.le
  have hcoef : N * (1 / N) ^ a = N ^ (1 - a) := by
    calc
      N * (1 / N) ^ a = N ^ (1 : ℝ) / N ^ a := by
        rw [one_div, Real.inv_rpow hNpos.le a]
        simp [div_eq_mul_inv]
      _ = N ^ (1 - a) := by rw [← Real.rpow_sub hNpos]
  calc
    (∑ i ∈ s, (x i) ^ a) = N * ((1 / N) * ∑ i ∈ s, (x i) ^ a) := by
      field_simp [hNpos.ne']
    _ ≤ N * ((1 / N) ^ a * (∑ i ∈ s, x i) ^ a) := hmul
    _ = N ^ (1 - a) * (∑ i ∈ s, x i) ^ a := by rw [← mul_assoc, hcoef]

lemma cell_product_moment_bound
    {ι : Type} (s : Finset ι) (n m R W : ℕ)
    (u v : ι → ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hR : 0 < R) (hcard : s.card = R)
    (hu : ∀ i ∈ s, R * u i ≤ n)
    (hv : ∑ i ∈ s, v i ≤ W * m) :
    ∑ i ∈ s, (((u i * v i : ℕ) : ℝ) ^ a) ≤
      (R : ℝ) ^ (1 - 2 * a) * (W : ℝ) ^ a *
        (((n * m : ℕ) : ℝ) ^ a) := by
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  have hun : ∀ i ∈ s, (u i : ℝ) ≤ (n : ℝ) / (R : ℝ) := by
    intro i hi
    rw [le_div_iff₀ hRR]
    have hcast : (R : ℝ) * (u i : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hu i hi
    simpa [mul_comm] using hcast
  have hmomb := sum_rpow_le_card_factor s (fun i ↦ (v i : ℝ)) ha0 ha1
    (fun i hi ↦ by positivity) (by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have : R = 0 := by simpa [hempty] using hcard.symm
      omega)
  rw [hcard] at hmomb
  have hvcast : (∑ i ∈ s, (v i : ℝ)) ≤ ((W * m : ℕ) : ℝ) := by
    exact_mod_cast hv
  have hmom : (∑ i ∈ s, ((v i : ℕ) : ℝ) ^ a) ≤
      (R : ℝ) ^ (1 - a) * (((W * m : ℕ) : ℝ) ^ a) :=
    hmomb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hvcast ha0) (by positivity))
  calc
    (∑ i ∈ s, (((u i * v i : ℕ) : ℝ) ^ a)) =
        ∑ i ∈ s, ((u i : ℝ) ^ a * (v i : ℝ) ^ a) := by
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      exact Real.mul_rpow (by positivity) (by positivity)
    _ ≤ ∑ i ∈ s, (((n : ℝ) / (R : ℝ)) ^ a * (v i : ℝ) ^ a) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) (hun i hi) ha0) (by positivity)
    _ = (((n : ℝ) / (R : ℝ)) ^ a) *
        ∑ i ∈ s, (v i : ℝ) ^ a := by rw [Finset.mul_sum]
    _ ≤ (((n : ℝ) / (R : ℝ)) ^ a) *
        ((R : ℝ) ^ (1 - a) * (((W * m : ℕ) : ℝ) ^ a)) := by
      gcongr
    _ = (R : ℝ) ^ (1 - 2 * a) * (W : ℝ) ^ a *
        (((n * m : ℕ) : ℝ) ^ a) := by
      rw [Real.div_rpow (by positivity) hRR.le]
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
      have hRpow : (R : ℝ) ^ (1 - a) / (R : ℝ) ^ a =
          (R : ℝ) ^ (1 - 2 * a) := by
        rw [← Real.rpow_sub hRR]
        congr 1
        ring
      calc
        (n : ℝ) ^ a / (R : ℝ) ^ a *
            ((R : ℝ) ^ (1 - a) * ((W : ℝ) ^ a * (m : ℝ) ^ a)) =
            ((R : ℝ) ^ (1 - a) / (R : ℝ) ^ a) * (W : ℝ) ^ a *
              ((n : ℝ) ^ a * (m : ℝ) ^ a) := by ring
        _ = _ := by rw [hRpow]

def incidenceExponent : ℝ := (69 : ℝ) / 100
def partitionJ : ℕ := 400
def partitionK : ℕ := 2 ^ 200
def partitionD : ℕ := 800 * 2 ^ 200
def cellNumber : ℕ := 2 ^ partitionJ
def crossingBudget : ℕ := partitionD + 1

lemma incidenceExponent_bounds :
    0 ≤ incidenceExponent ∧ incidenceExponent ≤ 1 := by
  norm_num [incidenceExponent]

lemma partition_fit (j : Fin partitionJ) :
    2 ^ (j : ℕ) < (partitionK + 1) ^ 2 := by
  have hj : (j : ℕ) < 400 := j.isLt
  have hpow : 2 ^ (j : ℕ) < 2 ^ 400 :=
    Nat.pow_lt_pow_right (by omega) hj
  calc
    2 ^ (j : ℕ) < 2 ^ 400 := hpow
    _ = (2 ^ 200) ^ 2 := by
      rw [show 400 = 200 * 2 by norm_num, pow_mul]
    _ < (2 ^ 200 + 1) ^ 2 := by
      nlinarith [show 0 < 2 ^ 200 by positivity]
    _ = (partitionK + 1) ^ 2 := by rfl

lemma exists_fixed_partition (S : Finset Point) :
    ∃ p : Fin partitionJ → Poly2,
      (∀ j, p j ≠ 0 ∧ (p j).totalDegree ≤ 2 * partitionK) ∧
      (partitionPolynomial p).totalDegree ≤ partitionD ∧
      ∀ sign : Fin partitionJ → Bool,
        cellNumber * (signCell S p sign).card ≤ S.card := by
  obtain ⟨p, hp, hcells⟩ :=
    exists_partition_cuts S partitionJ (fun _ ↦ partitionK) partition_fit
  refine ⟨p, hp, ?_, ?_⟩
  · calc
      (partitionPolynomial p).totalDegree ≤
          ∑ _j : Fin partitionJ, 2 * partitionK :=
        partitionPolynomial_totalDegree_le p (fun _ ↦ partitionK)
          (fun j ↦ (hp j).2)
      _ = partitionD := by norm_num [partitionJ, partitionK, partitionD]
  · simpa [cellNumber] using hcells

lemma partitionPolynomial_ne_zero_fixed
    {p : Fin partitionJ → Poly2}
    (hp : ∀ j, p j ≠ 0 ∧ (p j).totalDegree ≤ 2 * partitionK) :
    partitionPolynomial p ≠ 0 :=
  partitionPolynomial_ne_zero p (fun j ↦ (hp j).1)

lemma cellNumber_pos : 0 < cellNumber := by
  simp [cellNumber]

lemma card_sign_univ :
    (Finset.univ : Finset (Fin partitionJ → Bool)).card = cellNumber := by
  rw [Finset.card_univ, Fintype.card_fun]
  rw [Fintype.card_fin]
  simp [cellNumber, partitionJ]

lemma crossingBudget_le_pow : crossingBudget ≤ 2 ^ 210 := by
  norm_num [crossingBudget, partitionD]

lemma cellNumber_rpow_factor :
    (cellNumber : ℝ) ^ (1 - 2 * incidenceExponent) =
      (2 : ℝ) ^ (-152 : ℝ) := by
  change (((2 ^ 400 : ℕ) : ℝ) ^ (1 - 2 * ((69 : ℝ) / 100))) = _
  rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  norm_num

lemma pow210_rpow_incidenceExponent :
    (((2 ^ 210 : ℕ) : ℝ) ^ incidenceExponent) ≤ (2 : ℝ) ^ (145 : ℝ) := by
  change (((2 ^ 210 : ℕ) : ℝ) ^ ((69 : ℝ) / 100)) ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  norm_num

lemma incidence_contraction :
    (cellNumber : ℝ) ^ (1 - 2 * incidenceExponent) *
      (crossingBudget : ℝ) ^ incidenceExponent ≤ (1 : ℝ) / 8 := by
  have hW : (crossingBudget : ℝ) ≤ ((2 ^ 210 : ℕ) : ℝ) := by
    exact_mod_cast crossingBudget_le_pow
  have hWpow : (crossingBudget : ℝ) ^ incidenceExponent ≤
      (((2 ^ 210 : ℕ) : ℝ) ^ incidenceExponent) :=
    Real.rpow_le_rpow (by positivity) hW incidenceExponent_bounds.1
  calc
    (cellNumber : ℝ) ^ (1 - 2 * incidenceExponent) *
        (crossingBudget : ℝ) ^ incidenceExponent ≤
      (cellNumber : ℝ) ^ (1 - 2 * incidenceExponent) *
        (((2 ^ 210 : ℕ) : ℝ) ^ incidenceExponent) := by gcongr
    _ ≤ (2 : ℝ) ^ (-152 : ℝ) * (2 : ℝ) ^ (145 : ℝ) := by
      rw [cellNumber_rpow_factor]
      gcongr
      exact pow210_rpow_incidenceExponent
    _ = (1 : ℝ) / 128 := by
      rw [← Real.rpow_add (by positivity)]
      norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (1 : ℝ) / 8 := by norm_num

lemma rich_card_le_product_rpow {t b : ℕ} (ht : 1 ≤ t) (hb : 1 ≤ b)
    (hbt : b ≤ t ^ 2) :
    (b : ℝ) ≤ (((t * b : ℕ) : ℝ) ^ incidenceExponent) := by
  have htR : 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hbtR : (b : ℝ) ≤ (t : ℝ) ^ 2 := by exact_mod_cast hbt
  have hsmall : (b : ℝ) ^ (1 - incidenceExponent) ≤
      (t : ℝ) ^ incidenceExponent := by
    calc
      (b : ℝ) ^ (1 - incidenceExponent) ≤
          ((t : ℝ) ^ 2) ^ (1 - incidenceExponent) := by
        apply Real.rpow_le_rpow (by positivity) hbtR
        norm_num [incidenceExponent]
      _ = (t : ℝ) ^ (2 * (1 - incidenceExponent)) := by
        calc
          ((t : ℝ) ^ 2) ^ (1 - incidenceExponent) =
              ((t : ℝ) ^ (2 : ℝ)) ^ (1 - incidenceExponent) := by
                congr 1
                exact (Real.rpow_natCast (t : ℝ) 2).symm
          _ = _ := (Real.rpow_mul (by positivity) 2
            (1 - incidenceExponent)).symm
      _ ≤ (t : ℝ) ^ incidenceExponent := by
        apply Real.rpow_le_rpow_of_exponent_le htR
        norm_num [incidenceExponent]
  calc
    (b : ℝ) = (b : ℝ) ^ (1 : ℝ) := by simp
    _ = (b : ℝ) ^ incidenceExponent *
        (b : ℝ) ^ (1 - incidenceExponent) := by
      rw [← Real.rpow_add hbR]
      congr 1
      ring
    _ ≤ (b : ℝ) ^ incidenceExponent * (t : ℝ) ^ incidenceExponent := by
      gcongr
    _ = (((t * b : ℕ) : ℝ) ^ incidenceExponent) := by
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity), mul_comm]

def incidenceLinearConstant : ℕ := 2 * crossingBudget
def incidenceConstant : ℕ := 8 * incidenceLinearConstant

lemma partitionD_le_incidenceConstant : partitionD ≤ incidenceConstant := by
  simp [partitionD, incidenceConstant, incidenceLinearConstant, crossingBudget]

lemma direct_line_constant : partitionD + crossingBudget ≤ incidenceLinearConstant := by
  simp only [incidenceLinearConstant, crossingBudget]
  omega

lemma incidenceLinear_le_incidenceConstant :
    incidenceLinearConstant ≤ incidenceConstant := by
  simp only [incidenceConstant]
  omega

set_option linter.constructorNameAsVariable false in
/- A deliberately non-sharp planar point--line incidence estimate.  The
exponent `69/100` is chosen only to make the fixed polynomial-partition
recurrence contract. -/
theorem planar_incidence_bound
    (S : Finset Point) (L : Finset LineIndex)
    (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L) :
    (incidenceCount S L : ℝ) ≤
      incidenceConstant * (((S.card * L.card : ℕ) : ℝ) ^ incidenceExponent) +
        incidenceConstant * S.card + incidenceLinearConstant * L.card := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S L with
  | h n ih =>
      by_cases hS : S = ∅
      · subst S
        simp only [Nat.cast_mul] at hn
        subst n
        simp [incidenceCount, pointsOnLine]
        positivity
      obtain ⟨p, hp, hpdeg, hcells⟩ := exists_fixed_partition S
      let q := partitionPolynomial p
      let T : (Fin partitionJ → Bool) → Finset Point := fun sign ↦ signCell S p sign
      let B : (Fin partitionJ → Bool) → Finset LineIndex := fun sign ↦
        richCellLines L S p sign
      let u : (Fin partitionJ → Bool) → ℕ := fun sign ↦ (T sign).card
      let v : (Fin partitionJ → Bool) → ℕ := fun sign ↦ (B sign).card
      have hq0 : q ≠ 0 := partitionPolynomial_ne_zero_fixed hp
      have hqdeg : q.totalDegree ≤ partitionD := hpdeg
      have hBvalid (sign : Fin partitionJ → Bool) :
          ∀ l ∈ B sign, ValidLine l := by
        intro l hl
        exact hvalid l (mem_richCellLines_iff.mp hl).1
      have hBdistinct (sign : Fin partitionJ → Bool) : DistinctSupports (B sign) := by
        intro l hl m hm heq
        exact hdistinct (mem_richCellLines_iff.mp hl).1
          (mem_richCellLines_iff.mp hm).1 heq
      have hrec (sign : Fin partitionJ → Bool) :
          (incidenceCount (T sign) (B sign) : ℝ) ≤
            incidenceConstant * ((((T sign).card * (B sign).card : ℕ) : ℝ) ^
              incidenceExponent) + incidenceConstant * (T sign).card +
              incidenceLinearConstant * (B sign).card := by
        by_cases hB : B sign = ∅
        · rw [hB]
          simp only [card_empty, mul_zero, CharP.cast_eq_zero, add_zero]
          positivity
        · have hBne : (B sign).Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
          obtain ⟨l, hlB⟩ := hBne
          have ht2 : 2 ≤ (pointsOnLine (T sign) l).card := by
            simpa [B, T] using (mem_richCellLines_iff.mp hlB).2
          have htpos : 0 < (T sign).card :=
            lt_of_lt_of_le (by omega) (Finset.card_le_card
              (pointsOnLine_subset (T sign) l))
          have hRtwo : 2 ≤ cellNumber := by
            change 2 ≤ 2 ^ 400
            have := Nat.one_lt_pow (by omega : 400 ≠ 0) (by omega : 1 < 2)
            omega
          have hcell := hcells sign
          have htlt : (T sign).card < S.card := by
            change cellNumber * (T sign).card ≤ S.card at hcell
            nlinarith
          exact ih (T sign).card (by omega) (T sign) (B sign)
            (hBvalid sign) (hBdistinct sign) rfl
      have hvsum : ∑ sign : Fin partitionJ → Bool, v sign ≤
          crossingBudget * L.card := by
        calc
          ∑ sign : Fin partitionJ → Bool, v sign ≤
              ∑ sign : Fin partitionJ → Bool, (cellLines L S p sign).card := by
            apply Finset.sum_le_sum
            intro sign hs
            exact Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ crossingBudget * L.card :=
            sum_card_cellLines_le_degree L S p hpdeg
      have hmoment := cell_product_moment_bound
        (Finset.univ : Finset (Fin partitionJ → Bool)) S.card L.card
          cellNumber crossingBudget u v incidenceExponent_bounds.1
          incidenceExponent_bounds.2 cellNumber_pos card_sign_univ
          (fun sign _ ↦ by simpa [u, T] using hcells sign)
          (by simpa using hvsum)
      have hmoment' :
          ∑ sign : Fin partitionJ → Bool,
              (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) ≤
            (1 : ℝ) / 8 * (((S.card * L.card : ℕ) : ℝ) ^ incidenceExponent) := by
        calc
          _ ≤ (cellNumber : ℝ) ^ (1 - 2 * incidenceExponent) *
              (crossingBudget : ℝ) ^ incidenceExponent *
                (((S.card * L.card : ℕ) : ℝ) ^ incidenceExponent) := hmoment
          _ ≤ (1 : ℝ) / 8 *
                (((S.card * L.card : ℕ) : ℝ) ^ incidenceExponent) := by
            exact mul_le_mul_of_nonneg_right incidence_contraction (by positivity)
      have habsorb (sign : Fin partitionJ → Bool) :
          ((v sign : ℕ) : ℝ) ≤
            (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) := by
        by_cases hv0 : v sign = 0
        · rw [hv0]
          norm_num [incidenceExponent]
        · have hv1 : 1 ≤ v sign := Nat.one_le_iff_ne_zero.mpr hv0
          have hvle : v sign ≤ (u sign) ^ 2 := by
            simpa [v, u, T, B] using
              card_richCellLines_le_sq L S p sign hdistinct
          have hu1 : 1 ≤ u sign := by
            by_contra hu0
            have huz : u sign = 0 := by omega
            rw [huz] at hvle
            simp at hvle
            omega
          exact rich_card_le_product_rpow hu1 hv1 hvle
      have hcell (sign : Fin partitionJ → Bool) :
          (incidenceCount (T sign) L : ℝ) ≤
            (incidenceConstant + incidenceLinearConstant) *
                (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) +
              incidenceConstant * u sign +
              (cellLines L S p sign).card := by
        have hsplit := incidenceCount_cell_le_rich_add L S p sign
        have hsplitR : (incidenceCount (T sign) L : ℝ) ≤
            (incidenceCount (T sign) (B sign) : ℝ) +
              (cellLines L S p sign).card := by
          exact_mod_cast (by simpa [T, B] using hsplit)
        have hr := hrec sign
        have ha := habsorb sign
        change (incidenceCount (T sign) (B sign) : ℝ) ≤
            incidenceConstant * (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) +
              incidenceConstant * u sign + incidenceLinearConstant * v sign at hr
        calc
          (incidenceCount (T sign) L : ℝ) ≤
              (incidenceCount (T sign) (B sign) : ℝ) +
                (cellLines L S p sign).card := hsplitR
          _ ≤ (incidenceConstant *
                (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) +
              incidenceConstant * u sign + incidenceLinearConstant * v sign) +
                (cellLines L S p sign).card := by gcongr
          _ ≤ (incidenceConstant *
                (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) +
              incidenceConstant * u sign + incidenceLinearConstant *
                (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent)) +
                (cellLines L S p sign).card := by
              gcongr
          _ = _ := by ring
      have hcellsTotal :
          (∑ sign : Fin partitionJ → Bool,
              (incidenceCount (T sign) L : ℝ)) ≤
            (incidenceConstant + incidenceLinearConstant) *
                ∑ sign : Fin partitionJ → Bool,
                  (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) +
              incidenceConstant *
                ∑ sign : Fin partitionJ → Bool, (u sign : ℝ) +
              ∑ sign : Fin partitionJ → Bool,
                ((cellLines L S p sign).card : ℝ) := by
        calc
          ∑ sign : Fin partitionJ → Bool,
              (incidenceCount (T sign) L : ℝ) ≤
              ∑ sign : Fin partitionJ → Bool,
                ((incidenceConstant + incidenceLinearConstant) *
                    (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent) +
                  incidenceConstant * u sign +
                  (cellLines L S p sign).card) := by
            exact Finset.sum_le_sum fun sign _ ↦ hcell sign
          _ = _ := by
            simp only [Finset.sum_add_distrib]
            rw [Finset.mul_sum, Finset.mul_sum]
      have hpartition := incidenceCount_partition_le S L p
      have hwall := incidenceCount_wall_le q hq0 S L hvalid hdistinct
      have hwallR : (incidenceCount (wallPoints S q) L : ℝ) ≤
          partitionD * ((wallPoints S q).card + L.card) := by
        have hwNat : incidenceCount (wallPoints S q) L ≤
            partitionD * ((wallPoints S q).card + L.card) :=
          hwall.trans (Nat.mul_le_mul_right _ hqdeg)
        exact_mod_cast hwNat
      have hpoints := wall_add_sum_cells_le S p
      change (wallPoints S q).card +
          ∑ sign : Fin partitionJ → Bool, u sign ≤ S.card at hpoints
      have hpointsR : ((wallPoints S q).card : ℝ) +
          ∑ sign : Fin partitionJ → Bool, (u sign : ℝ) ≤ S.card := by
        exact_mod_cast hpoints
      have hcrossR : (∑ sign : Fin partitionJ → Bool,
          ((cellLines L S p sign).card : ℝ)) ≤ crossingBudget * L.card := by
        exact_mod_cast (sum_card_cellLines_le_degree L S p hpdeg)
      have hpartitionR : (incidenceCount S L : ℝ) ≤
          (incidenceCount (wallPoints S q) L : ℝ) +
            ∑ sign : Fin partitionJ → Bool, (incidenceCount (T sign) L : ℝ) := by
        change incidenceCount S L ≤ incidenceCount (wallPoints S q) L +
            ∑ sign : Fin partitionJ → Bool, incidenceCount (T sign) L at hpartition
        exact_mod_cast hpartition
      have hA : (incidenceLinearConstant : ℝ) ≤ incidenceConstant := by
        exact_mod_cast incidenceLinear_le_incidenceConstant
      have hD : (partitionD : ℝ) ≤ incidenceConstant := by
        exact_mod_cast partitionD_le_incidenceConstant
      have hdirect : (partitionD + crossingBudget : ℝ) ≤
          incidenceLinearConstant := by exact_mod_cast direct_line_constant
      let X : ℝ := ∑ sign : Fin partitionJ → Bool,
        (((u sign * v sign : ℕ) : ℝ) ^ incidenceExponent)
      let Y : ℝ := ∑ sign : Fin partitionJ → Bool, (u sign : ℝ)
      let Z : ℝ := ∑ sign : Fin partitionJ → Bool,
        ((cellLines L S p sign).card : ℝ)
      let w : ℝ := (wallPoints S q).card
      let r : ℝ := (((S.card * L.card : ℕ) : ℝ) ^ incidenceExponent)
      change X ≤ (1 : ℝ) / 8 * r at hmoment'
      change w + Y ≤ S.card at hpointsR
      change Z ≤ crossingBudget * L.card at hcrossR
      change (incidenceCount (wallPoints S q) L : ℝ) ≤
        partitionD * (w + L.card) at hwallR
      change (∑ sign : Fin partitionJ → Bool,
          (incidenceCount (T sign) L : ℝ)) ≤
        (incidenceConstant + incidenceLinearConstant) * X +
          incidenceConstant * Y + Z at hcellsTotal
      have hnonlinear :
          (incidenceConstant + incidenceLinearConstant : ℝ) * X ≤
            incidenceConstant * r := by
        have htwice : (incidenceConstant + incidenceLinearConstant : ℝ) ≤
            2 * incidenceConstant := by linarith
        have hnonneg : 0 ≤ X := by
          exact Finset.sum_nonneg fun _ _ ↦
            Real.rpow_nonneg (Nat.cast_nonneg _) _
        calc
          _ ≤ (2 * incidenceConstant : ℝ) *
              X := by
            exact mul_le_mul_of_nonneg_right htwice hnonneg
          _ ≤ (2 * incidenceConstant : ℝ) *
              ((1 : ℝ) / 8 * r) := by
            exact mul_le_mul_of_nonneg_left hmoment'
              (mul_nonneg (by norm_num)
                (by exact_mod_cast Nat.zero_le incidenceConstant))
          _ ≤ incidenceConstant * r := by
            have hroot : 0 ≤ r := by
              exact Real.rpow_nonneg (Nat.cast_nonneg _) _
            calc
              (2 * incidenceConstant : ℝ) * ((1 : ℝ) / 8 * r) =
                  ((incidenceConstant : ℝ) / 4) * r := by ring
              _ ≤ incidenceConstant * r := by
                apply mul_le_mul_of_nonneg_right _ hroot
                have hc : (0 : ℝ) ≤ incidenceConstant := by
                  exact_mod_cast Nat.zero_le incidenceConstant
                linarith
      have hfinal : (incidenceCount S L : ℝ) ≤
          partitionD * (w + L.card) +
            ((incidenceConstant + incidenceLinearConstant) * X +
              incidenceConstant * Y + Z) := by
        calc
          (incidenceCount S L : ℝ) ≤
              (incidenceCount (wallPoints S q) L : ℝ) +
                ∑ sign : Fin partitionJ → Bool,
                  (incidenceCount (T sign) L : ℝ) := hpartitionR
          _ ≤ partitionD * (w + L.card) +
                ((incidenceConstant + incidenceLinearConstant) * X +
                  incidenceConstant * Y + Z) :=
            add_le_add hwallR hcellsTotal
      calc
        (incidenceCount S L : ℝ) ≤
            partitionD * (w + L.card) +
              ((incidenceConstant + incidenceLinearConstant) * X +
                incidenceConstant * Y + Z) := hfinal
        _ ≤ incidenceConstant * r +
            incidenceConstant * S.card + incidenceLinearConstant * L.card := by
          have hpointterm : (partitionD : ℝ) * w +
                incidenceConstant * Y ≤
              incidenceConstant * S.card := by
            have hw0 : 0 ≤ w := Nat.cast_nonneg (wallPoints S q).card
            calc
              _ ≤ incidenceConstant * w + incidenceConstant * Y := by
                exact add_le_add (mul_le_mul_of_nonneg_right hD hw0) (le_refl _)
              _ = incidenceConstant * (w + Y) := by ring
              _ ≤ incidenceConstant * S.card := by
                exact mul_le_mul_of_nonneg_left hpointsR
                  (by exact_mod_cast Nat.zero_le incidenceConstant)
          have hlineterm : (partitionD : ℝ) * L.card +
                Z ≤
              incidenceLinearConstant * L.card := by
            calc
              _ ≤ (partitionD : ℝ) * (L.card : ℝ) +
                    (crossingBudget : ℝ) * (L.card : ℝ) := by
                exact add_le_add (le_refl _) hcrossR
              _ = (partitionD + crossingBudget) * L.card := by ring
              _ ≤ incidenceLinearConstant * L.card := by
                exact mul_le_mul_of_nonneg_right hdirect (Nat.cast_nonneg L.card)
          calc
            partitionD * (w + L.card) +
                ((incidenceConstant + incidenceLinearConstant) * X +
                  incidenceConstant * Y + Z) =
                ((incidenceConstant + incidenceLinearConstant) * X) +
                  ((partitionD : ℝ) * w + incidenceConstant * Y) +
                  ((partitionD : ℝ) * L.card + Z) := by ring
            _ ≤ incidenceConstant * r +
                incidenceConstant * S.card + incidenceLinearConstant * L.card := by
              exact add_le_add (add_le_add hnonlinear hpointterm) hlineterm
        _ = incidenceConstant *
              (((n * L.card : ℕ) : ℝ) ^ incidenceExponent) +
            incidenceConstant * n + incidenceLinearConstant * L.card := by
          rw [← hn]

/-! ## Richness order statistics -/

def richerOrEqual (S : Finset Point) (l m : LineIndex) : Bool :=
  decide ((pointsOnLine S m).card ≤ (pointsOnLine S l).card)

/-- The lines, in nonincreasing order of their number of selected points. -/
noncomputable def orderedLines (S : Finset Point) (L : Finset LineIndex) :
    List LineIndex :=
  L.toList.mergeSort (richerOrEqual S)

lemma orderedLines_perm (S : Finset Point) (L : Finset LineIndex) :
    (orderedLines S L).Perm L.toList := by
  exact List.mergeSort_perm _ _

@[simp] lemma length_orderedLines (S : Finset Point) (L : Finset LineIndex) :
    (orderedLines S L).length = L.card := by
  rw [orderedLines, List.length_mergeSort, Finset.length_toList]

lemma orderedLines_nodup (S : Finset Point) (L : Finset LineIndex) :
    (orderedLines S L).Nodup := by
  exact (orderedLines_perm S L).nodup_iff.mpr L.nodup_toList

lemma mem_orderedLines_iff {S : Finset Point} {L : Finset LineIndex}
    {l : LineIndex} : l ∈ orderedLines S L ↔ l ∈ L := by
  rw [(orderedLines_perm S L).mem_iff, Finset.mem_toList]

lemma orderedLines_pairwise (S : Finset Point) (L : Finset LineIndex) :
    (orderedLines S L).Pairwise (fun l m ↦ richerOrEqual S l m = true) := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simp only [richerOrEqual, decide_eq_true_eq] at hab hbc ⊢
    omega
  · intro a b
    simp only [richerOrEqual, Bool.or_eq_true, decide_eq_true_eq]
    omega

/-- The first `k` richest lines. -/
noncomputable def initialLines (S : Finset Point) (L : Finset LineIndex)
    (k : ℕ) : Finset LineIndex :=
  ((orderedLines S L).take k).toFinset

lemma initialLines_subset (S : Finset Point) (L : Finset LineIndex) (k : ℕ) :
    initialLines S L k ⊆ L := by
  intro l hl
  rw [initialLines, List.mem_toFinset] at hl
  exact mem_orderedLines_iff.mp (List.mem_of_mem_take hl)

lemma card_initialLines {S : Finset Point} {L : Finset LineIndex} {k : ℕ}
    (hk : k ≤ L.card) : (initialLines S L k).card = k := by
  classical
  have hn : ((orderedLines S L).take k).Nodup :=
    (orderedLines_nodup S L).take
  rw [initialLines, List.toFinset_card_of_nodup hn, List.length_take,
    length_orderedLines, min_eq_left hk]

lemma initialLines_distinct {S : Finset Point} {L : Finset LineIndex}
    (hdistinct : DistinctSupports L) (k : ℕ) :
    DistinctSupports (initialLines S L k) := by
  intro l hl m hm h
  exact hdistinct (initialLines_subset S L k hl)
    (initialLines_subset S L k hm) h

lemma initialLines_valid {S : Finset Point} {L : Finset LineIndex}
    (hvalid : ∀ l ∈ L, ValidLine l) (k : ℕ) :
    ∀ l ∈ initialLines S L k, ValidLine l := by
  intro l hl
  exact hvalid l (initialLines_subset S L k hl)

lemma ordered_get_mem {S : Finset Point} {L : Finset LineIndex}
    (i : Fin (orderedLines S L).length) : (orderedLines S L).get i ∈ L := by
  exact mem_orderedLines_iff.mp (List.get_mem _ i)

lemma initial_occupancy_ge {S : Finset Point} {L : Finset LineIndex}
    {i : ℕ} (hi : i < (orderedLines S L).length) {l : LineIndex}
    (hl : l ∈ initialLines S L (i + 1)) :
    (pointsOnLine S (orderedLines S L)[i]).card ≤
      (pointsOnLine S l).card := by
  rw [initialLines, List.mem_toFinset, List.mem_take_iff_getElem] at hl
  obtain ⟨j, hj, hjl⟩ := hl
  have hjlen : j < (orderedLines S L).length := by omega
  by_cases hji : j = i
  · subst j
    simpa [hjl]
  · have hji' : j < i := by omega
    have hrel := (orderedLines_pairwise S L).rel_get_of_lt
      (a := ⟨j, hjlen⟩) (b := ⟨i, hi⟩) hji'
    simp only [richerOrEqual, decide_eq_true_eq] at hrel
    simpa [List.get_eq_getElem, hjl] using hrel

lemma rank_mul_occupancy_le_incidence {S : Finset Point}
    {L : Finset LineIndex} {i : ℕ}
    (hi : i < (orderedLines S L).length) :
    (i + 1) * (pointsOnLine S (orderedLines S L)[i]).card ≤
      incidenceCount S (initialLines S L (i + 1)) := by
  classical
  rw [incidenceCount]
  calc
    (i + 1) * (pointsOnLine S (orderedLines S L)[i]).card =
        ∑ _l ∈ initialLines S L (i + 1),
          (pointsOnLine S (orderedLines S L)[i]).card := by
      rw [Finset.sum_const, card_initialLines (by simpa using Nat.succ_le_iff.mpr hi)]
      simp [mul_comm]
    _ ≤ ∑ l ∈ initialLines S L (i + 1), (pointsOnLine S l).card := by
      apply Finset.sum_le_sum
      intro l hl
      exact initial_occupancy_ge hi hl

lemma rank_occupancy_union_bound {S : Finset Point}
    {L : Finset LineIndex} (hdistinct : DistinctSupports L) {i : ℕ}
    (hi : i < (orderedLines S L).length) :
    (i + 1) * (pointsOnLine S (orderedLines S L)[i]).card ≤
      S.card + (i + 1) ^ 2 := by
  calc
    _ ≤ incidenceCount S (initialLines S L (i + 1)) :=
      rank_mul_occupancy_le_incidence hi
    _ ≤ S.card + (initialLines S L (i + 1)).card ^ 2 :=
      incidenceCount_le_card_add_sq S _ (initialLines_distinct hdistinct _)
    _ = S.card + (i + 1) ^ 2 := by
      rw [card_initialLines (by simpa using Nat.succ_le_iff.mpr hi)]

lemma rank_occupancy_partition_bound {S : Finset Point}
    {L : Finset LineIndex} (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L) {i : ℕ}
    (hi : i < (orderedLines S L).length) :
    ((i + 1) : ℝ) * (pointsOnLine S (orderedLines S L)[i]).card ≤
      incidenceConstant * (((S.card * (i + 1) : ℕ) : ℝ) ^ incidenceExponent) +
        incidenceConstant * S.card + incidenceLinearConstant * (i + 1) := by
  have hlower := rank_mul_occupancy_le_incidence hi
  have hupper := planar_incidence_bound S (initialLines S L (i + 1))
    (initialLines_valid hvalid _) (initialLines_distinct hdistinct _)
  rw [card_initialLines (by simpa using Nat.succ_le_iff.mpr hi)] at hupper
  have hlowerR :
      ((((i + 1) * (pointsOnLine S (orderedLines S L)[i]).card : ℕ) : ℝ)) ≤
        (incidenceCount S (initialLines S L (i + 1)) : ℝ) := by
    exact_mod_cast hlower
  norm_num only [Nat.cast_mul] at hlowerR
  simpa only [Nat.cast_add, Nat.cast_one] using hlowerR.trans hupper

/-- The number of points on the line of zero-based rank `i`, or zero beyond
the end of the ordered list.  The total definition makes finite sums over
ordinary intervals considerably easier to manipulate. -/
noncomputable def rankedOccupancy (S : Finset Point) (L : Finset LineIndex)
    (i : ℕ) : ℕ :=
  if hi : i < (orderedLines S L).length then
    (pointsOnLine S (orderedLines S L)[i]).card
  else 0

@[simp] lemma rankedOccupancy_eq {S : Finset Point} {L : Finset LineIndex}
    {i : ℕ} (hi : i < (orderedLines S L).length) :
    rankedOccupancy S L i = (pointsOnLine S (orderedLines S L)[i]).card := by
  have hi' : i < L.card := by simpa using hi
  simp [rankedOccupancy, hi']

lemma sum_rankedOccupancy_eq (S : Finset Point) (L : Finset LineIndex)
    (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range L.card, f (rankedOccupancy S L i) =
      ∑ l ∈ L, f (pointsOnLine S l).card := by
  classical
  rw [← length_orderedLines]
  rw [Finset.sum_range]
  conv_lhs =>
    enter [2, i]
    rw [rankedOccupancy_eq i.isLt]
  calc
    _ = ((orderedLines S L).map
        (fun l ↦ f (pointsOnLine S l).card)).sum :=
      Fin.sum_univ_fun_getElem _ _
    _ = (L.toList.map (fun l ↦ f (pointsOnLine S l).card)).sum :=
      ((orderedLines_perm S L).map
        (fun l ↦ f (pointsOnLine S l).card)).sum_eq
    _ = _ := by
      simpa using (List.sum_toFinset
        (fun l ↦ f (pointsOnLine S l).card) L.nodup_toList).symm

lemma sum_rankedOccupancy_cast_eq (S : Finset Point) (L : Finset LineIndex)
    (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range L.card, f (rankedOccupancy S L i) =
      ∑ l ∈ L, f (pointsOnLine S l).card := by
  classical
  rw [← length_orderedLines]
  rw [Finset.sum_range]
  conv_lhs =>
    enter [2, i]
    rw [rankedOccupancy_eq i.isLt]
  calc
    _ = ((orderedLines S L).map
        (fun l ↦ f (pointsOnLine S l).card)).sum :=
      Fin.sum_univ_fun_getElem _ _
    _ = (L.toList.map (fun l ↦ f (pointsOnLine S l).card)).sum :=
      ((orderedLines_perm S L).map
        (fun l ↦ f (pointsOnLine S l).card)).sum_eq
    _ = _ := by
      simpa using (List.sum_toFinset
        (fun l ↦ f (pointsOnLine S l).card) L.nodup_toList).symm

lemma sum_Ico_succ_inv_sq_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) ≤
      ((a : ℝ)⁻¹) := by
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-2 : ℝ))
      (Set.Icc (a : ℝ) (b : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono (by
      intro x hx
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      exact lt_of_lt_of_le ha0 hx.1)
  have hsum := hanti.sum_le_integral_Ico hab
  rw [integral_rpow] at hsum
  · calc
      _ ≤ ((b : ℝ) ^ ((-2 : ℝ) + 1) -
          (a : ℝ) ^ ((-2 : ℝ) + 1)) / ((-2 : ℝ) + 1) := hsum
      _ = (a : ℝ)⁻¹ - (b : ℝ)⁻¹ := by
        rw [show (-2 : ℝ) + 1 = -1 by norm_num]
        rw [Real.rpow_neg_one, Real.rpow_neg_one]
        ring
      _ ≤ (a : ℝ)⁻¹ := by
        have hb0 : 0 ≤ (b : ℝ)⁻¹ := by positivity
        linarith
  · right
    constructor
    · norm_num
    · have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
      rw [Set.uIcc_of_le habR]
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inl (not_le_of_gt ha0)

lemma sum_Ico_one_succ_inv_sq_le (q : ℕ) :
    (∑ i ∈ Finset.Ico 1 q, (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) ≤
      (25 : ℝ) / 36 := by
  by_cases hq : 3 ≤ q
  · let f : ℕ → ℝ := fun i ↦ (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ))
    have hsplit := Finset.sum_range_add_sum_Ico f hq
    have htail := sum_Ico_succ_inv_sq_le (a := 3) (b := q) (by omega) hq
    have hone : ∑ i ∈ Finset.Ico 1 q, f i = ∑ i ∈ Finset.range q, f i - 1 := by
      rw [Finset.sum_Ico_eq_sub f (by omega)]
      norm_num [f]
    have hfirst : ∑ i ∈ Finset.range 3, f i = (49 : ℝ) / 36 := by
      norm_num [f, Real.rpow_intCast]
    rw [hfirst] at hsplit
    have hthreecast : (((3 : ℕ) : ℝ)) = 3 := by norm_num
    rw [hthreecast] at htail
    have hthird : ((3 : ℝ)⁻¹) = 1 / 3 := by norm_num
    rw [hthird] at htail
    rw [hone]
    linarith
  · interval_cases q <;> norm_num [Real.rpow_intCast]

lemma sum_Ico_succ_rpow_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b,
        (((i + 1 : ℕ) : ℝ) ^ (-(31 : ℝ) / 50))) ≤
      (50 : ℝ) / 19 * (b : ℝ) ^ ((19 : ℝ) / 50) := by
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-(31 : ℝ) / 50))
      (Set.Icc (a : ℝ) (b : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono (by
      intro x hx
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      exact lt_of_lt_of_le ha0 hx.1)
  have hsum := hanti.sum_le_integral_Ico hab
  rw [integral_rpow] at hsum
  · calc
      _ ≤ ((b : ℝ) ^ (-(31 : ℝ) / 50 + 1) -
          (a : ℝ) ^ (-(31 : ℝ) / 50 + 1)) /
            (-(31 : ℝ) / 50 + 1) := hsum
      _ = ((b : ℝ) ^ ((19 : ℝ) / 50) -
          (a : ℝ) ^ ((19 : ℝ) / 50)) / ((19 : ℝ) / 50) := by
        congr 2 <;> norm_num
      _ ≤ (50 : ℝ) / 19 * (b : ℝ) ^ ((19 : ℝ) / 50) := by
        have ha0 : 0 ≤ (a : ℝ) ^ ((19 : ℝ) / 50) := Real.rpow_nonneg (by positivity) _
        nlinarith
  · left
    norm_num

lemma choose_two_cast_le_half_sq (r : ℕ) :
    (r.choose 2 : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by
  have h : 2 * r.choose 2 = r * (r - 1) := by
    rw [mul_comm 2, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
  have hR := congrArg (fun z : ℕ ↦ (z : ℝ)) h
  push_cast at hR
  have hsub : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
  have hmul : (r : ℝ) * (r - 1 : ℕ) ≤ (r : ℝ) * r :=
    mul_le_mul_of_nonneg_left hsub (by positivity)
  nlinarith

lemma add_three_sq_le (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

lemma rankedOccupancy_union_div_bound {S : Finset Point}
    {L : Finset LineIndex} (hdistinct : DistinctSupports L) {i : ℕ}
    (hi : i < L.card) :
    (rankedOccupancy S L i : ℝ) ≤
      (S.card : ℝ) / (i + 1) + (i + 1) := by
  have hi' : i < (orderedLines S L).length := by simpa using hi
  have h := rank_occupancy_union_bound hdistinct hi'
  rw [← rankedOccupancy_eq hi'] at h
  have hR : ((i + 1 : ℕ) : ℝ) * (rankedOccupancy S L i : ℝ) ≤
      (S.card : ℝ) + ((i + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h
  have hj : (0 : ℝ) < (i + 1 : ℕ) := by positivity
  have hR' : (rankedOccupancy S L i : ℝ) * ((i + 1 : ℕ) : ℝ) ≤
      (S.card : ℝ) + ((i + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [mul_comm] using hR
  calc
    _ ≤ ((S.card : ℝ) + ((i + 1 : ℕ) : ℝ) ^ 2) / (i + 1 : ℕ) :=
      (le_div_iff₀ hj).2 hR'
    _ = (S.card : ℝ) / (i + 1) + (i + 1) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      <;> ring_nf

lemma rankedOccupancy_sq_union_bound {S : Finset Point}
    {L : Finset LineIndex} (hdistinct : DistinctSupports L) {i : ℕ}
    (hi : i < L.card) :
    (rankedOccupancy S L i : ℝ) ^ 2 ≤
      (S.card : ℝ) ^ 2 * (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
        2 * S.card + ((i + 1 : ℕ) : ℝ) ^ 2 := by
  have h := rankedOccupancy_union_div_bound (S := S) hdistinct hi
  have hr0 : (0 : ℝ) ≤ rankedOccupancy S L i := by positivity
  have hj0 : (0 : ℝ) ≤ (i + 1 : ℕ) := by positivity
  have hsq : (rankedOccupancy S L i : ℝ) ^ 2 ≤
      ((S.card : ℝ) / (i + 1) + (i + 1)) ^ 2 :=
    (sq_le_sq₀ hr0 (by positivity)).2 h
  calc
    _ ≤ ((S.card : ℝ) / (i + 1) + (i + 1)) ^ 2 := hsq
    _ = (S.card : ℝ) ^ 2 * (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
        2 * S.card + ((i + 1 : ℕ) : ℝ) ^ 2 := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      <;> ring

lemma sum_rankedOccupancy_sq_early_le {S : Finset Point}
    {L : Finset LineIndex} (hdistinct : DistinctSupports L)
    (hrich : ∀ l ∈ L, 2 * (pointsOnLine S l).card < S.card)
    {q : ℕ} (hq : q ≤ L.card) :
    (∑ i ∈ Finset.range q, (rankedOccupancy S L i : ℝ) ^ 2) ≤
      (17 : ℝ) / 18 * S.card ^ 2 + 2 * S.card * q + (q : ℝ) ^ 3 := by
  by_cases hq0 : q = 0
  · subst q
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_pow]
    positivity
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  have hm1 : 1 ≤ L.card := hq1.trans hq
  have hi0 : 0 < (orderedLines S L).length := by simpa using hm1
  have hl0 := ordered_get_mem (S := S) (L := L) ⟨0, hi0⟩
  have hr0N := hrich _ hl0
  have hr0 : 2 * (rankedOccupancy S L 0 : ℝ) < S.card := by
    rw [rankedOccupancy_eq hi0]
    exact_mod_cast hr0N
  have hfirst : (rankedOccupancy S L 0 : ℝ) ^ 2 ≤
      (S.card : ℝ) ^ 2 / 4 := by
    have hn0 : (0 : ℝ) ≤ S.card := by positivity
    have hro0 : (0 : ℝ) ≤ rankedOccupancy S L 0 := by positivity
    nlinarith [sq_nonneg ((S.card : ℝ) - 2 * rankedOccupancy S L 0)]
  let f : ℕ → ℝ := fun i ↦ (rankedOccupancy S L i : ℝ) ^ 2
  have hsplit := Finset.sum_range_add_sum_Ico f hq1
  have hterm : ∀ i ∈ Finset.Ico 1 q,
      f i ≤ (S.card : ℝ) ^ 2 * (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
        2 * S.card + ((i + 1 : ℕ) : ℝ) ^ 2 := by
    intro i hi
    apply rankedOccupancy_sq_union_bound hdistinct
    exact lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hq
  have htail := Finset.sum_le_sum hterm
  have hinv := sum_Ico_one_succ_inv_sq_le q
  have hsqterms : (∑ i ∈ Finset.Ico 1 q, (((i + 1 : ℕ) : ℝ) ^ 2)) ≤
      ((Finset.Ico 1 q).card : ℝ) * (q : ℝ) ^ 2 := by
    have h := Finset.sum_le_card_nsmul (Finset.Ico 1 q)
      (fun i ↦ (((i + 1 : ℕ) : ℝ) ^ 2)) ((q : ℝ) ^ 2) (by
        intro i hi
        exact pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast (Finset.mem_Ico.mp hi).2) 2)
    simpa only [nsmul_eq_mul] using h
  have hcard : (((Finset.Ico 1 q).card : ℕ) : ℝ) ≤ q := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le q 1
  have htail' : (∑ i ∈ Finset.Ico 1 q, f i) ≤
      (25 : ℝ) / 36 * S.card ^ 2 + 2 * S.card * q + (q : ℝ) ^ 3 := by
    calc
      _ ≤ ∑ i ∈ Finset.Ico 1 q,
          ((S.card : ℝ) ^ 2 * (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
            2 * S.card + ((i + 1 : ℕ) : ℝ) ^ 2) := htail
      _ = (S.card : ℝ) ^ 2 *
            (∑ i ∈ Finset.Ico 1 q, (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) +
          ((Finset.Ico 1 q).card : ℝ) * (2 * S.card) +
          (∑ i ∈ Finset.Ico 1 q, (((i + 1 : ℕ) : ℝ) ^ 2)) := by
        simp_rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        have hn2 : 0 ≤ (S.card : ℝ) ^ 2 := sq_nonneg _
        have hn : 0 ≤ (S.card : ℝ) := by positivity
        have hqR : 0 ≤ (q : ℝ) := by positivity
        have hinvMul := mul_le_mul_of_nonneg_left hinv hn2
        have htwoN : 0 ≤ 2 * (S.card : ℝ) := mul_nonneg (by norm_num) hn
        have hconst := mul_le_mul_of_nonneg_right hcard htwoN
        have hsqcard := mul_le_mul_of_nonneg_right hcard (sq_nonneg (q : ℝ))
        nlinarith [hinvMul, hconst, hsqterms, hsqcard]
  dsimp [f] at hsplit htail'
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.sum_empty, zero_add] at hsplit
  simp only [Finset.sum_singleton] at hsplit
  nlinarith

lemma incidence_rank_nonlinear_sq (n : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    (incidenceConstant * ((((n * j : ℕ) : ℝ) ^ incidenceExponent)) / j) ^ 2 =
      incidenceConstant ^ 2 * (n : ℝ) ^ ((69 : ℝ) / 50) *
        (j : ℝ) ^ (-(31 : ℝ) / 50) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [show (((n * j : ℕ) : ℝ)) = (n : ℝ) * j by norm_num]
  rw [Real.mul_rpow hn0 hj0]
  calc
    (incidenceConstant * ((n : ℝ) ^ incidenceExponent *
        (j : ℝ) ^ incidenceExponent) / j) ^ 2 =
        incidenceConstant ^ 2 * ((n : ℝ) ^ incidenceExponent) ^ 2 *
          (((j : ℝ) ^ incidenceExponent) ^ 2 / (j : ℝ) ^ 2) := by ring
    _ = incidenceConstant ^ 2 * (n : ℝ) ^
          (incidenceExponent * (2 : ℝ)) *
      ((j : ℝ) ^ (incidenceExponent * (2 : ℝ)) /
            (j : ℝ) ^ (2 : ℝ)) := by
      rw [Real.rpow_mul hn0, Real.rpow_mul hj0]
      norm_num
    _ = incidenceConstant ^ 2 * (n : ℝ) ^
          (incidenceExponent * (2 : ℝ)) *
          (j : ℝ) ^ (incidenceExponent * (2 : ℝ) - 2) := by
      rw [Real.rpow_sub hjpos]
    _ = _ := by
      rw [incidenceExponent]
      congr 2 <;> norm_num

lemma incidence_rank_linear_sq (n : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    (incidenceConstant * (n : ℝ) / j) ^ 2 =
      incidenceConstant ^ 2 * (n : ℝ) ^ 2 * (j : ℝ) ^ (-2 : ℝ) := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  field_simp
  <;> ring

lemma rankedOccupancy_partition_div_bound {S : Finset Point}
    {L : Finset LineIndex} (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L) {i : ℕ} (hi : i < L.card) :
    (rankedOccupancy S L i : ℝ) ≤
      incidenceConstant * ((((S.card * (i + 1) : ℕ) : ℝ) ^ incidenceExponent)) /
          (i + 1) +
        incidenceConstant * S.card / (i + 1) + incidenceLinearConstant := by
  have hi' : i < (orderedLines S L).length := by simpa using hi
  have h := rank_occupancy_partition_bound hvalid hdistinct hi'
  rw [← rankedOccupancy_eq hi'] at h
  have hj : (0 : ℝ) < (i + 1 : ℕ) := by positivity
  have h' : (rankedOccupancy S L i : ℝ) * ((i + 1 : ℕ) : ℝ) ≤
      incidenceConstant * ((((S.card * (i + 1) : ℕ) : ℝ) ^ incidenceExponent)) +
        incidenceConstant * S.card + incidenceLinearConstant * (i + 1) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc
    _ ≤ (incidenceConstant *
          ((((S.card * (i + 1) : ℕ) : ℝ) ^ incidenceExponent)) +
        incidenceConstant * S.card + incidenceLinearConstant * (i + 1)) /
          (((i + 1 : ℕ) : ℝ)) := (le_div_iff₀ hj).2 h'
    _ = _ := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      <;> ring

lemma rankedOccupancy_sq_partition_bound {S : Finset Point}
    {L : Finset LineIndex} (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L) {i : ℕ} (hi : i < L.card) :
    (rankedOccupancy S L i : ℝ) ^ 2 ≤ 3 *
      (incidenceConstant ^ 2 * (S.card : ℝ) ^ ((69 : ℝ) / 50) *
          (((i + 1 : ℕ) : ℝ) ^ (-(31 : ℝ) / 50)) +
        incidenceConstant ^ 2 * (S.card : ℝ) ^ 2 *
          (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
        incidenceLinearConstant ^ 2) := by
  let x : ℝ := incidenceConstant *
    ((((S.card * (i + 1) : ℕ) : ℝ) ^ incidenceExponent)) / (i + 1)
  let y : ℝ := incidenceConstant * S.card / (i + 1)
  let z : ℝ := incidenceLinearConstant
  have hr := rankedOccupancy_partition_div_bound (S := S) hvalid hdistinct hi
  have hr0 : (0 : ℝ) ≤ rankedOccupancy S L i := by positivity
  have hxyz0 : 0 ≤ x + y + z := by
    dsimp [x, y, z]
    positivity
  have hsq : (rankedOccupancy S L i : ℝ) ^ 2 ≤ (x + y + z) ^ 2 :=
    (sq_le_sq₀ hr0 hxyz0).2 (by simpa [x, y, z] using hr)
  calc
    _ ≤ (x + y + z) ^ 2 := hsq
    _ ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := add_three_sq_le x y z
    _ = _ := by
      rw [show x ^ 2 = incidenceConstant ^ 2 *
          (S.card : ℝ) ^ ((69 : ℝ) / 50) *
            (((i + 1 : ℕ) : ℝ) ^ (-(31 : ℝ) / 50)) by
          simpa [x, Nat.succ_eq_add_one] using
            (incidence_rank_nonlinear_sq S.card (Nat.succ_le_succ (Nat.zero_le i))),
        show y ^ 2 = incidenceConstant ^ 2 * (S.card : ℝ) ^ 2 *
          (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) by
          simpa [y, Nat.succ_eq_add_one] using
            (incidence_rank_linear_sq S.card (Nat.succ_le_succ (Nat.zero_le i)))]

lemma sum_rankedOccupancy_sq_tail_le {S : Finset Point}
    {L : Finset LineIndex} (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L) {q : ℕ} (hq1 : 1 ≤ q)
    (hqm : q ≤ L.card) :
    (∑ i ∈ Finset.Ico q L.card, (rankedOccupancy S L i : ℝ) ^ 2) ≤ 3 *
      (incidenceConstant ^ 2 * (S.card : ℝ) ^ ((69 : ℝ) / 50) *
          ((50 : ℝ) / 19 * (L.card : ℝ) ^ ((19 : ℝ) / 50)) +
        incidenceConstant ^ 2 * (S.card : ℝ) ^ 2 * (q : ℝ)⁻¹ +
        incidenceLinearConstant ^ 2 * L.card) := by
  have hterm : ∀ i ∈ Finset.Ico q L.card,
      (rankedOccupancy S L i : ℝ) ^ 2 ≤ 3 *
        (incidenceConstant ^ 2 * (S.card : ℝ) ^ ((69 : ℝ) / 50) *
            (((i + 1 : ℕ) : ℝ) ^ (-(31 : ℝ) / 50)) +
          incidenceConstant ^ 2 * (S.card : ℝ) ^ 2 *
            (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
          incidenceLinearConstant ^ 2) := by
    intro i hi
    apply rankedOccupancy_sq_partition_bound hvalid hdistinct
    exact (Finset.mem_Ico.mp hi).2
  have hsum := Finset.sum_le_sum hterm
  have hpow := sum_Ico_succ_rpow_le hq1 hqm
  have hinv := sum_Ico_succ_inv_sq_le hq1 hqm
  have hcard : (((Finset.Ico q L.card).card : ℕ) : ℝ) ≤ L.card := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le L.card q
  calc
    _ ≤ ∑ i ∈ Finset.Ico q L.card, 3 *
        (incidenceConstant ^ 2 * (S.card : ℝ) ^ ((69 : ℝ) / 50) *
            (((i + 1 : ℕ) : ℝ) ^ (-(31 : ℝ) / 50)) +
          incidenceConstant ^ 2 * (S.card : ℝ) ^ 2 *
            (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) +
          incidenceLinearConstant ^ 2) := hsum
    _ = 3 * (incidenceConstant ^ 2 * (S.card : ℝ) ^ ((69 : ℝ) / 50) *
          (∑ i ∈ Finset.Ico q L.card,
            (((i + 1 : ℕ) : ℝ) ^ (-(31 : ℝ) / 50))) +
        incidenceConstant ^ 2 * (S.card : ℝ) ^ 2 *
          (∑ i ∈ Finset.Ico q L.card,
            (((i + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) +
        ((Finset.Ico q L.card).card : ℝ) * incidenceLinearConstant ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.mul_sum, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hA : 0 ≤ (incidenceConstant : ℝ) ^ 2 := sq_nonneg _
      have hn69 : 0 ≤ (S.card : ℝ) ^ ((69 : ℝ) / 50) :=
        Real.rpow_nonneg (by positivity) _
      have hn2 : 0 ≤ (S.card : ℝ) ^ 2 := sq_nonneg _
      have hE : 0 ≤ (incidenceLinearConstant : ℝ) ^ 2 := sq_nonneg _
      have hpow' := mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hn69)
      have hinv' := mul_le_mul_of_nonneg_left hinv (mul_nonneg hA hn2)
      have hcard' := mul_le_mul_of_nonneg_right hcard hE
      nlinarith

open Filter Topology

noncomputable def separationError (n : ℕ) : ℝ :=
    (3 + 3 * (incidenceConstant : ℝ) ^ 2) * ((Nat.sqrt n : ℝ)⁻¹) +
    (3 * (incidenceConstant : ℝ) ^ 2 * ((50 : ℝ) / 19)) *
      (n : ℝ) ^ (-((3 : ℝ) / 250)) +
    (3 * (incidenceLinearConstant : ℝ) ^ 2) * (n : ℝ) ^ (-((2 : ℝ) / 5))

lemma tendsto_nat_sqrt_cast_atTop :
    Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b * b, ?_⟩
  intro a ha
  exact Nat.le_sqrt.mpr ha

lemma tendsto_separationError_zero :
    Tendsto separationError atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ ((Nat.sqrt n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_nat_sqrt_cast_atTop.inv_tendsto_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-((3 : ℝ) / 250)))
      atTop (𝓝 0) :=
    by simpa only [Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 250)).comp
        tendsto_natCast_atTop_atTop)
  have hlinear : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-((2 : ℝ) / 5)))
      atTop (𝓝 0) :=
    by simpa only [Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
        tendsto_natCast_atTop_atTop)
  have h1 := hsqrt.const_mul (3 + 3 * (incidenceConstant : ℝ) ^ 2)
  have h2 := hsmall.const_mul
    (3 * (incidenceConstant : ℝ) ^ 2 * ((50 : ℝ) / 19))
  have h3 := hlinear.const_mul (3 * (incidenceLinearConstant : ℝ) ^ 2)
  change Tendsto (fun n : ℕ ↦
    (3 + 3 * (incidenceConstant : ℝ) ^ 2) * ((Nat.sqrt n : ℝ)⁻¹) +
      (3 * (incidenceConstant : ℝ) ^ 2 * ((50 : ℝ) / 19)) *
        (n : ℝ) ^ (-((3 : ℝ) / 250)) +
      (3 * (incidenceLinearConstant : ℝ) ^ 2) *
        (n : ℝ) ^ (-((2 : ℝ) / 5))) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using (h1.add h2).add h3

lemma separationError_eventually_small :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, separationError n < (1 : ℝ) / 36 := by
  have ht := tendsto_separationError_zero
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨n₀, hn₀⟩ := ht (1 / 36) (by norm_num)
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hdist := hn₀ n hn
  rw [Real.dist_eq, sub_zero] at hdist
  have herr0 : 0 ≤ separationError n := by
    dsimp [separationError]
    positivity
  simpa [abs_of_nonneg herr0] using hdist

lemma sqrt_error_le {n : ℕ} (hn : 1 ≤ n) :
    2 * (n : ℝ) * Nat.sqrt n + (Nat.sqrt n : ℝ) ^ 3 ≤
      (n : ℝ) ^ 2 * (3 * (Nat.sqrt n : ℝ)⁻¹) := by
  have hqposN : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have hqpos : (0 : ℝ) < Nat.sqrt n := by exact_mod_cast hqposN
  have hq2N := Nat.sqrt_le n
  have hq2mul : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by exact_mod_cast hq2N
  have hq2 : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by simpa [pow_two] using hq2mul
  have hq4 : (Nat.sqrt n : ℝ) ^ 4 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self (sq_nonneg (Nat.sqrt n : ℝ)) hq2]
  have heq : (n : ℝ) ^ 2 * (3 * (Nat.sqrt n : ℝ)⁻¹) =
      (3 * (n : ℝ) ^ 2) / Nat.sqrt n := by
    field_simp
    <;> ring
  rw [heq, le_div_iff₀ hqpos]
  nlinarith

lemma incidence_power_product_le {n m : ℕ} (hn : 1 ≤ n)
    (hm : (m : ℝ) ≤ (n : ℝ) ^ ((8 : ℝ) / 5)) :
    (n : ℝ) ^ ((69 : ℝ) / 50) * (m : ℝ) ^ ((19 : ℝ) / 50) ≤
      (n : ℝ) ^ ((497 : ℝ) / 250) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hp : (0 : ℝ) ≤ 19 / 50 := by norm_num
  have hmPow := Real.rpow_le_rpow hm0 hm hp
  calc
    _ ≤ (n : ℝ) ^ ((69 : ℝ) / 50) *
        (((n : ℝ) ^ ((8 : ℝ) / 5)) ^ ((19 : ℝ) / 50)) :=
      mul_le_mul_of_nonneg_left hmPow (Real.rpow_nonneg hn0 _)
    _ = (n : ℝ) ^ ((69 : ℝ) / 50) *
        (n : ℝ) ^ (((8 : ℝ) / 5) * ((19 : ℝ) / 50)) := by
      rw [← Real.rpow_mul hn0]
    _ = (n : ℝ) ^ (((69 : ℝ) / 50) +
        ((8 : ℝ) / 5) * ((19 : ℝ) / 50)) := by
      rw [Real.rpow_add hnpos]
    _ = _ := by congr 2 <;> norm_num

lemma sq_mul_small_rpow {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 * (n : ℝ) ^ (-((3 : ℝ) / 250)) =
      (n : ℝ) ^ ((497 : ℝ) / 250) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hnpos]
  congr 2 <;> norm_num

lemma sq_mul_linear_rpow {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 * (n : ℝ) ^ (-((2 : ℝ) / 5)) =
      (n : ℝ) ^ ((8 : ℝ) / 5) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hnpos]
  congr 2 <;> norm_num

theorem sum_rankedOccupancy_sq_lt {S : Finset Point}
    {L : Finset LineIndex} (hvalid : ∀ l ∈ L, ValidLine l)
    (hdistinct : DistinctSupports L)
    (hrich : ∀ l ∈ L, 2 * (pointsOnLine S l).card < S.card)
    (hn : 1 ≤ S.card)
    (hm : (L.card : ℝ) ≤ (S.card : ℝ) ^ ((8 : ℝ) / 5))
    (herr : separationError S.card < (1 : ℝ) / 36) :
    (∑ i ∈ Finset.range L.card, (rankedOccupancy S L i : ℝ) ^ 2) <
      (35 : ℝ) / 36 * S.card ^ 2 := by
  let q := Nat.sqrt S.card
  have hqposN : 0 < q := by
    dsimp [q]
    exact Nat.sqrt_pos.mpr (by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposN
  have hn2pos : (0 : ℝ) < (S.card : ℝ) ^ 2 := sq_pos_of_pos (by positivity)
  have herrMul : (S.card : ℝ) ^ 2 * separationError S.card <
      (S.card : ℝ) ^ 2 * ((1 : ℝ) / 36) :=
    mul_lt_mul_of_pos_left herr hn2pos
  have hsqrt := sqrt_error_le hn
  change 2 * (S.card : ℝ) * q + (q : ℝ) ^ 3 ≤
    (S.card : ℝ) ^ 2 * (3 * (q : ℝ)⁻¹) at hsqrt
  have hbase : 3 * (q : ℝ)⁻¹ ≤ separationError S.card := by
    dsimp [separationError]
    have hqinv : 0 ≤ (q : ℝ)⁻¹ := by positivity
    have hA : 0 ≤ (incidenceConstant : ℝ) ^ 2 := sq_nonneg _
    have hnsmall : 0 ≤ (S.card : ℝ) ^ (-((3 : ℝ) / 250)) :=
      Real.rpow_nonneg (by positivity) _
    have hnlinear : 0 ≤ (S.card : ℝ) ^ (-((2 : ℝ) / 5)) :=
      Real.rpow_nonneg (by positivity) _
    have hE : 0 ≤ (incidenceLinearConstant : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  by_cases hmq : L.card ≤ q
  · have hearly := sum_rankedOccupancy_sq_early_le hdistinct hrich
      (q := L.card) (le_refl _)
    have hmR : (L.card : ℝ) ≤ q := by exact_mod_cast hmq
    have hm3 : (L.card : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hmR 3
    have hearlyErr : 2 * (S.card : ℝ) * L.card + (L.card : ℝ) ^ 3 ≤
        (S.card : ℝ) ^ 2 * (3 * (q : ℝ)⁻¹) := by
      have hn0 : (0 : ℝ) ≤ S.card := by positivity
      have hcoef : 0 ≤ 2 * (S.card : ℝ) := mul_nonneg (by norm_num) hn0
      have hmul := mul_le_mul_of_nonneg_left hmR hcoef
      nlinarith
    have hbaseMul := mul_le_mul_of_nonneg_left hbase (le_of_lt hn2pos)
    nlinarith
  · have hqm : q ≤ L.card := by omega
    have hearly := sum_rankedOccupancy_sq_early_le hdistinct hrich hqm
    have htail := sum_rankedOccupancy_sq_tail_le (S := S) hvalid hdistinct
      (Nat.one_le_iff_ne_zero.mpr (by omega : q ≠ 0)) hqm
    let f : ℕ → ℝ := fun i ↦ (rankedOccupancy S L i : ℝ) ^ 2
    have hsplit := Finset.sum_range_add_sum_Ico f hqm
    have hpower := incidence_power_product_le hn hm
    let C : ℝ := 3 * (incidenceConstant : ℝ) ^ 2 * ((50 : ℝ) / 19)
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    have hnonlinear :
        3 * ((incidenceConstant : ℝ) ^ 2 *
          (S.card : ℝ) ^ ((69 : ℝ) / 50) *
          ((50 : ℝ) / 19 * (L.card : ℝ) ^ ((19 : ℝ) / 50))) ≤
        (S.card : ℝ) ^ 2 *
          (C * (S.card : ℝ) ^ (-((3 : ℝ) / 250))) := by
      have hmul := mul_le_mul_of_nonneg_left hpower hC0
      calc
        _ = C * ((S.card : ℝ) ^ ((69 : ℝ) / 50) *
            (L.card : ℝ) ^ ((19 : ℝ) / 50)) := by dsimp [C]; ring
        _ ≤ C * (S.card : ℝ) ^ ((497 : ℝ) / 250) := hmul
        _ = (S.card : ℝ) ^ 2 *
            (C * (S.card : ℝ) ^ (-((3 : ℝ) / 250))) := by
          rw [← sq_mul_small_rpow hn]
          ring
    have hlinear :
        3 * ((incidenceConstant : ℝ) ^ 2 * (S.card : ℝ) ^ 2 *
          (q : ℝ)⁻¹) =
        (S.card : ℝ) ^ 2 *
          (3 * (incidenceConstant : ℝ) ^ 2 * (q : ℝ)⁻¹) := by ring
    have hE0 : 0 ≤ 3 * (incidenceLinearConstant : ℝ) ^ 2 := by positivity
    have hEbound :
        3 * ((incidenceLinearConstant : ℝ) ^ 2 * (L.card : ℝ)) ≤
        (S.card : ℝ) ^ 2 *
          (3 * (incidenceLinearConstant : ℝ) ^ 2 *
            (S.card : ℝ) ^ (-((2 : ℝ) / 5))) := by
      have hmul := mul_le_mul_of_nonneg_left hm hE0
      calc
        _ = (3 * (incidenceLinearConstant : ℝ) ^ 2) * L.card := by ring
        _ ≤ (3 * (incidenceLinearConstant : ℝ) ^ 2) *
            (S.card : ℝ) ^ ((8 : ℝ) / 5) := hmul
        _ = (S.card : ℝ) ^ 2 *
            (3 * (incidenceLinearConstant : ℝ) ^ 2 *
              (S.card : ℝ) ^ (-((2 : ℝ) / 5))) := by
          rw [← sq_mul_linear_rpow hn]
          ring
    have hsumError :
        (∑ i ∈ Finset.range L.card, (rankedOccupancy S L i : ℝ) ^ 2) ≤
          (17 : ℝ) / 18 * S.card ^ 2 +
            (S.card : ℝ) ^ 2 * separationError S.card := by
      dsimp [f] at hsplit
      dsimp [separationError, C] at hnonlinear ⊢
      nlinarith [hsqrt, htail, hnonlinear, hlinear, hEbound]
    nlinarith

lemma choose_two_cast_gt_thirtyfive_sq_div_seventytwo {n : ℕ} (hn : 37 ≤ n) :
    (35 : ℝ) / 72 * (n : ℝ) ^ 2 < (n.choose 2 : ℝ) := by
  have h : 2 * n.choose 2 = n * (n - 1) := by
    rw [mul_comm 2, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  have hR := congrArg (fun z : ℕ ↦ (z : ℝ)) h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hR
  rw [Nat.cast_sub (by omega : 1 ≤ n)] at hR
  norm_num only [Nat.cast_one] at hR
  have hnR : (37 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- A quantitative Beck-type consequence of the polynomial-partition incidence
bound.  If distinct valid lines partition all pairs of a sufficiently large
finite point set and no line contains half the points, then there are more than
`n^(8/5)` lines. -/
theorem many_lines_of_pair_partition :
    ∃ n₀ : ℕ, ∀ (S : Finset Point) (L : Finset LineIndex), n₀ ≤ S.card →
      (∀ l ∈ L, ValidLine l) → DistinctSupports L →
      (∀ l ∈ L, 2 * (pointsOnLine S l).card < S.card) →
      S.card.choose 2 = ∑ l ∈ L, (pointsOnLine S l).card.choose 2 →
      (S.card : ℝ) ^ ((8 : ℝ) / 5) < L.card := by
  obtain ⟨nerr, hnerr⟩ := separationError_eventually_small
  refine ⟨max nerr 37, ?_⟩
  intro S L hn hvalid hdistinct hrich hpair
  have hnerr' : nerr ≤ S.card := (le_max_left _ _).trans hn
  have hn37 : 37 ≤ S.card := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ S.card := by omega
  have herr := hnerr S.card hnerr'
  by_contra hnot
  have hm : (L.card : ℝ) ≤ (S.card : ℝ) ^ ((8 : ℝ) / 5) := le_of_not_gt hnot
  have hsq := sum_rankedOccupancy_sq_lt hvalid hdistinct hrich hn1 hm herr
  have hrankNat : S.card.choose 2 =
      ∑ i ∈ Finset.range L.card, (rankedOccupancy S L i).choose 2 := by
    calc
      _ = ∑ l ∈ L, (pointsOnLine S l).card.choose 2 := hpair
      _ = _ := (sum_rankedOccupancy_eq S L (fun r ↦ r.choose 2)).symm
  have hrank : (S.card.choose 2 : ℝ) =
      ∑ i ∈ Finset.range L.card, ((rankedOccupancy S L i).choose 2 : ℝ) := by
    exact_mod_cast hrankNat
  have hchoose :
      (∑ i ∈ Finset.range L.card,
        ((rankedOccupancy S L i).choose 2 : ℝ)) ≤
      (∑ i ∈ Finset.range L.card,
        (rankedOccupancy S L i : ℝ) ^ 2) / 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range L.card,
          ((rankedOccupancy S L i : ℝ) ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact choose_two_cast_le_half_sq _
      _ = _ := by rw [Finset.sum_div]
  have hlower := choose_two_cast_gt_thirtyfive_sq_div_seventytwo hn37
  rw [hrank] at hlower
  nlinarith

end

end Erdos606.PlanarIncidence
