/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixSmallBallAssembly

/-!
# Finite reindexing from Gaussian deviations to excursion profiles

This file isolates the purely finite change of variables used after the
Gaussian lattice small-ball estimate.  A deviation `x` at level `l` is sent
to the natural-valued excursion count

`m_l = 2*l^2 + x`.

The recursive sum `certifiedProfileBlockPartition` has exactly the same
finite branching tree as `GaussianSmallBall.gaussianBoxPartition`, but its
edge weights are the certified Taylor minorants from
`AppendixSmallBallAssembly`.  The main bridge theorem proves, by finite
induction, that any checked one-edge Gaussian comparison multiplies and sums
over the whole constrained block.  Thus the only analytic input left at this
interface is a local Stirling/Taylor-to-fixed-Gaussian comparison; there is no
remaining path reindexing or probabilistic assumption.
-/

open scoped BigOperators

namespace Erdos1165.GaussianProfileReindex

noncomputable section

open AppendixFirstMoment AppendixSmallBallAssembly GaussianSmallBall

/-- The excursion-profile entry associated to an integer deviation from the
parabolic center. -/
def centeredProfileValue (l : ℕ) (x : ℤ) : ℕ :=
  Int.toNat ((profileCenter l : ℤ) + x)

lemma centeredProfileValue_cast {l : ℕ} {x : ℤ}
    (hx : -(profileCenter l : ℤ) ≤ x) :
    (centeredProfileValue l x : ℤ) = (profileCenter l : ℤ) + x := by
  rw [centeredProfileValue, Int.toNat_of_nonneg]
  omega

lemma centeredProfileValue_sub_center {l : ℕ} {x : ℤ}
    (hx : -(profileCenter l : ℤ) ≤ x) :
    (centeredProfileValue l x : ℤ) - profileCenter l = x := by
  rw [centeredProfileValue_cast hx]
  omega

lemma centeredProfileValue_in_window {l R : ℕ} {x : ℤ} {delta : ℝ}
    (hx : x ∈ gaussianBox R) (hcenter : R ≤ profileCenter l)
    (hwidth : (R : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    InProfileWindow delta l (centeredProfileValue l x) := by
  have hbox := (mem_gaussianBox.mp hx)
  have hxLower : -(profileCenter l : ℤ) ≤ x := by
    exact_mod_cast (show -(profileCenter l : ℤ) ≤ x by omega)
  rw [InProfileWindow]
  have hdev : (centeredProfileValue l x : ℝ) - profileCenter l = (x : ℝ) := by
    exact_mod_cast centeredProfileValue_sub_center hxLower
  rw [hdev]
  have habs : |x| ≤ (R : ℤ) := by
    rw [abs_le]
    exact hbox
  have habsReal : |(x : ℝ)| ≤ R := by exact_mod_cast habs
  exact habsReal.trans hwidth

lemma centeredProfileValue_injective_on_box {l R : ℕ} {x y : ℤ}
    (hx : x ∈ gaussianBox R) (hy : y ∈ gaussianBox R)
    (hcenter : R ≤ profileCenter l)
    (hxy : centeredProfileValue l x = centeredProfileValue l y) : x = y := by
  have hxLower : -(profileCenter l : ℤ) ≤ x := by
    have := (mem_gaussianBox.mp hx).1
    omega
  have hyLower : -(profileCenter l : ℤ) ≤ y := by
    have := (mem_gaussianBox.mp hy).1
    omega
  have hcast := congrArg (fun z : ℕ ↦ (z : ℤ)) hxy
  rw [centeredProfileValue_cast hxLower, centeredProfileValue_cast hyLower] at hcast
  omega

/-! ## A finite type of killed Gaussian paths -/

/-- Paths in the same finite branching tree used by
`gaussianBoxPartition`.  The unit subtype records that the current position
is in the box; a successor additionally records a boxed displacement and the
remaining path from the new position. -/
def GaussianBoxPath (R : ℕ) : (steps : ℕ) → ℤ → Type
  | 0, x => {u : Unit // x ∈ gaussianBox R}
  | steps + 1, x =>
      {u : Unit // x ∈ gaussianBox R} ×
        Σ d : ↥(gaussianBox R), GaussianBoxPath R steps (x + d.1)

noncomputable instance gaussianBoxPathFintype (R : ℕ) :
    ∀ (steps : ℕ) (x : ℤ), Fintype (GaussianBoxPath R steps x)
  | 0, x => by
      change Fintype {u : Unit // x ∈ gaussianBox R}
      infer_instance
  | steps + 1, x => by
      letI (d : ↥(gaussianBox R)) :
          Fintype (GaussianBoxPath R steps (x + d.1)) :=
        gaussianBoxPathFintype R steps (x + d.1)
      change Fintype
        ({u : Unit // x ∈ gaussianBox R} ×
          Σ d : ↥(gaussianBox R), GaussianBoxPath R steps (x + d.1))
      infer_instance

lemma gaussianBoxPath_mem {R steps : ℕ} {x : ℤ}
    (p : GaussianBoxPath R steps x) : x ∈ gaussianBox R := by
  cases steps with
  | zero => exact p.2
  | succ steps => exact p.1.2

/-- Profile values along a finite Gaussian box path, including both its
initial and terminal positions. -/
def gaussianBoxPathValues (l : ℕ) :
    {steps : ℕ} → {x : ℤ} → GaussianBoxPath R steps x → List ℕ
  | 0, x, _ => [centeredProfileValue l x]
  | _steps + 1, x, p =>
      centeredProfileValue l x ::
        gaussianBoxPathValues (l + 1) p.2.2

@[simp] lemma gaussianBoxPathValues_length (l : ℕ)
    {steps : ℕ} {x : ℤ} (p : GaussianBoxPath R steps x) :
    (gaussianBoxPathValues l p).length = steps + 1 := by
  induction steps generalizing l x with
  | zero => rfl
  | succ steps ih =>
      rw [gaussianBoxPathValues, List.length_cons, ih]

@[simp] lemma gaussianBoxPathValues_head? (l : ℕ)
    {steps : ℕ} {x : ℤ} (p : GaussianBoxPath R steps x) :
    (gaussianBoxPathValues l p).head? = some (centeredProfileValue l x) := by
  cases steps <;> simp [gaussianBoxPathValues]

/-- Position of a killed path at a time between zero and `steps`. -/
def gaussianBoxPathPosition :
    {steps : ℕ} → {x : ℤ} → GaussianBoxPath R steps x → Fin (steps + 1) → ℤ
  | 0, x, _p, _j => x
  | _steps + 1, x, p, j =>
      Fin.cases x (fun k ↦ gaussianBoxPathPosition p.2.2 k) j

lemma gaussianBoxPathPosition_mem {R steps : ℕ} {x : ℤ}
    (p : GaussianBoxPath R steps x) (j : Fin (steps + 1)) :
    gaussianBoxPathPosition p j ∈ gaussianBox R := by
  induction steps generalizing x with
  | zero =>
      simpa [gaussianBoxPathPosition] using gaussianBoxPath_mem p
  | succ steps ih =>
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · simpa [gaussianBoxPathPosition] using p.1.2
      · simpa [gaussianBoxPathPosition] using ih p.2.2 k

lemma gaussianBoxPathValues_get (l : ℕ) {steps : ℕ} {x : ℤ}
    (p : GaussianBoxPath R steps x) (j : Fin (steps + 1)) :
    (gaussianBoxPathValues l p).get
        ⟨j.1, by simpa [gaussianBoxPathValues_length] using j.2⟩ =
      centeredProfileValue (l + j.1) (gaussianBoxPathPosition p j) := by
  induction steps generalizing l x with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp [gaussianBoxPathValues, gaussianBoxPathPosition]
  | succ steps ih =>
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · simp [gaussianBoxPathValues, gaussianBoxPathPosition]
      · simpa [gaussianBoxPathValues, gaussianBoxPathPosition, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
          using ih (l := l + 1) p.2.2 k

/-- Multiplicative certified Taylor weight of a path. -/
def gaussianBoxPathCertifiedWeight (l : ℕ) :
    {steps : ℕ} → {x : ℤ} → GaussianBoxPath R steps x → ℝ
  | 0, _x, _p => 1
  | _steps + 1, x, p =>
      certifiedTaylorEdge
          (centeredProfileValue l x)
          (centeredProfileValue (l + 1) (x + p.2.1.1)) *
        gaussianBoxPathCertifiedWeight (l + 1) p.2.2

lemma gaussianBoxPathCertifiedWeight_eq_product (l : ℕ)
    {steps : ℕ} {x : ℤ} (p : GaussianBoxPath R steps x) :
    gaussianBoxPathCertifiedWeight l p =
      certifiedTaylorProduct (gaussianBoxPathValues l p) := by
  induction steps generalizing l x with
  | zero => rfl
  | succ steps ih =>
      rw [gaussianBoxPathCertifiedWeight, gaussianBoxPathValues]
      have htail := gaussianBoxPathValues_length (l + 1) p.2.2
      cases hlist : gaussianBoxPathValues (l + 1) p.2.2 with
      | nil => simp [hlist] at htail
      | cons a rest =>
          have ha : a = centeredProfileValue (l + 1) (x + p.2.1.1) := by
            have hhead := gaussianBoxPathValues_head? (l + 1) p.2.2
            rw [hlist] at hhead
            exact Option.some.inj hhead
          subst a
          rw [certifiedTaylorProduct_cons_cons, ih, hlist]

lemma gaussianBoxPathValues_injective
    {R l steps : ℕ} {x : ℤ} (hcenter : R ≤ profileCenter l) :
    Function.Injective
      (gaussianBoxPathValues (R := R) (steps := steps) (x := x) l) := by
  induction steps generalizing l x with
  | zero =>
      intro p q h
      change {u : Unit // x ∈ gaussianBox R} at p q
      exact Subsingleton.elim p q
  | succ steps ih =>
      rintro ⟨px, d, ptail⟩ ⟨qx, e, qtail⟩ hvalues
      have htailValues :
          gaussianBoxPathValues (l + 1) ptail =
            gaussianBoxPathValues (l + 1) qtail := by
        simpa only [gaussianBoxPathValues, List.cons.injEq, true_and] using hvalues
      have hnextCenter : R ≤ profileCenter (l + 1) := by
        unfold profileCenter at hcenter ⊢
        exact hcenter.trans (by gcongr; omega)
      have hdpos : x + d.1 ∈ gaussianBox R := gaussianBoxPath_mem ptail
      have hepos : x + e.1 ∈ gaussianBox R := gaussianBoxPath_mem qtail
      have hhead : centeredProfileValue (l + 1) (x + d.1) =
          centeredProfileValue (l + 1) (x + e.1) := by
        have := congrArg List.head? htailValues
        rw [gaussianBoxPathValues_head?, gaussianBoxPathValues_head?] at this
        exact Option.some.inj this
      have hde : d = e := by
        apply Subtype.ext
        have := centeredProfileValue_injective_on_box hdpos hepos hnextCenter hhead
        omega
      subst e
      have htail : ptail = qtail :=
        ih hnextCenter htailValues
      subst qtail
      have hpq : px = qx := Subsingleton.elim _ _
      subst qx
      rfl

/-! ## Embedding a late Gaussian block into a full HLOZ profile -/

/-- Extend a Gaussian deviation path to a full profile by using the exact
parabolic center at all scales before `start`. -/
def embeddedGaussianPathProfile {start steps R : ℕ} (hstart : 2 ≤ start)
    (p : GaussianBoxPath R steps 0) : Profile (start + steps) :=
  fun i ↦
    if hi : i.1 < start - 2 then profileCenter (scaleIndex i)
    else
      centeredProfileValue (scaleIndex i)
        (gaussianBoxPathPosition p
          ⟨i.1 - (start - 2), by omega⟩)

lemma embeddedGaussianPathProfile_prefix {start steps R : ℕ}
    (hstart : 2 ≤ start) (p : GaussianBoxPath R steps 0)
    (i : Fin (start + steps - 1)) (hi : scaleIndex i < start) :
    embeddedGaussianPathProfile hstart p i = profileCenter (scaleIndex i) := by
  have hi' : i.1 < start - 2 := by
    unfold scaleIndex at hi
    omega
  simp [embeddedGaussianPathProfile, hi']

lemma embeddedGaussianPathProfile_block {start steps R : ℕ}
    (hstart : 2 ≤ start) (p : GaussianBoxPath R steps 0)
    (j : Fin (steps + 1)) :
    embeddedGaussianPathProfile hstart p
        ⟨start - 2 + j.1, by
          have hright : start + steps - 1 = start - 2 + (steps + 1) := by omega
          rw [hright]
          exact Nat.add_lt_add_left j.2 (start - 2)⟩ =
      centeredProfileValue (start + j.1) (gaussianBoxPathPosition p j) := by
  have hs : start - 2 + 2 = start := Nat.sub_add_cancel hstart
  let i : Fin (start + steps - 1) :=
    ⟨start - 2 + j.1, by
      have hright : start + steps - 1 = start - 2 + (steps + 1) := by omega
      rw [hright]
      exact Nat.add_lt_add_left j.2 (start - 2)⟩
  change embeddedGaussianPathProfile hstart p i = _
  unfold embeddedGaussianPathProfile
  rw [dif_neg (by dsimp only [i]; omega)]
  have hscale : scaleIndex i = start + j.1 := by
    unfold scaleIndex
    change start - 2 + j.1 + 2 = start + j.1
    omega
  have hfin :
      (⟨i.1 - (start - 2), by omega⟩ : Fin (steps + 1)) = j := by
    apply Fin.ext
    change (start - 2 + j.1) - (start - 2) = j.1
    omega
  rw [hscale, hfin]

lemma embeddedGaussianPathProfile_mem_constrainedProfiles
    {start steps R : ℕ} (hstart : 2 ≤ start)
    (p : GaussianBoxPath R steps 0) {delta : ℝ}
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    embeddedGaussianPathProfile hstart p ∈
      constrainedProfiles (start + steps) delta := by
  rw [mem_constrainedProfiles]
  intro i
  by_cases hi : i.1 < start - 2
  · have hiScale : scaleIndex i < start := by
      unfold scaleIndex
      omega
    rw [embeddedGaussianPathProfile_prefix hstart p i hiScale]
    unfold InProfileWindow
    simp only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, sub_self, abs_zero]
    exact Real.rpow_nonneg (by positivity) _
  · let j : Fin (steps + 1) :=
      ⟨i.1 - (start - 2), by omega⟩
    have hjScale : start + j.1 = scaleIndex i := by
      dsimp only [j]
      unfold scaleIndex
      have hs : start - 2 + 2 = start := Nat.sub_add_cancel hstart
      omega
    have hjMem : start + j.1 ∈ Finset.Icc start (start + steps) := by
      rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    have hpMem := gaussianBoxPathPosition_mem p j
    rw [show embeddedGaussianPathProfile hstart p i =
        centeredProfileValue (start + j.1) (gaussianBoxPathPosition p j) by
      unfold embeddedGaussianPathProfile
      rw [dif_neg hi]
      rw [← hjScale]]
    rw [← hjScale]
    exact centeredProfileValue_in_window hpMem
      (hcenter (start + j.1) hjMem) (hwidth (start + j.1) hjMem)

lemma embeddedGaussianPathProfile_injective
    {start steps R : ℕ} (hstart : 2 ≤ start)
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l) :
    Function.Injective
      (embeddedGaussianPathProfile (start := start) (steps := steps) (R := R) hstart) := by
  intro p q hpq
  apply gaussianBoxPathValues_injective (hcenter start (by simp))
  apply List.ext_get
  · simp only [gaussianBoxPathValues_length]
  · intro k hkp hkq
    let j : Fin (steps + 1) := ⟨k, by simpa [gaussianBoxPathValues_length] using hkp⟩
    rw [gaussianBoxPathValues_get start p j,
      gaussianBoxPathValues_get start q j]
    have hjMem : start + j.1 ∈ Finset.Icc start (start + steps) := by
      simp only [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    have hentry := congrFun hpq (⟨start - 2 + j.1, by omega⟩ :
      Fin (start + steps - 1))
    simpa only [embeddedGaussianPathProfile_block hstart] using hentry

/-- Sum of the deterministic logarithmic losses on a consecutive block. -/
def blockErrorSum (edgeError : ℕ → ℝ) (start : ℕ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 => edgeError start + blockErrorSum edgeError (start + 1) steps

@[simp] lemma blockErrorSum_zero (edgeError : ℕ → ℝ) (start : ℕ) :
    blockErrorSum edgeError start 0 = 0 := rfl

@[simp] lemma blockErrorSum_succ (edgeError : ℕ → ℝ) (start steps : ℕ) :
    blockErrorSum edgeError start (steps + 1) =
      edgeError start + blockErrorSum edgeError (start + 1) steps := rfl

/-- The finite excursion-profile block sum obtained from the same deviation
tree as `gaussianBoxPartition`.  Intermediate deviations and increments are
both restricted to `[-R,R]`; leaving the box kills the branch. -/
def certifiedProfileBlockPartition (start : ℕ) : ℕ → ℕ → ℤ → ℝ
  | 0, R, x => if x ∈ gaussianBox R then 1 else 0
  | steps + 1, R, x =>
      if x ∈ gaussianBox R then
        ∑ d ∈ gaussianBox R,
          certifiedTaylorEdge
              (centeredProfileValue start x)
              (centeredProfileValue (start + 1) (x + d)) *
            certifiedProfileBlockPartition (start + 1) steps R (x + d)
      else 0

lemma certifiedProfileBlockPartition_nonneg (start steps R : ℕ) (x : ℤ) :
    0 ≤ certifiedProfileBlockPartition start steps R x := by
  induction steps generalizing start x with
  | zero =>
      simp only [certifiedProfileBlockPartition]
      split_ifs <;> positivity
  | succ steps ih =>
      simp only [certifiedProfileBlockPartition]
      split_ifs
      · exact Finset.sum_nonneg fun d _ ↦
          mul_nonneg (certifiedTaylorEdge_nonneg _ _)
            (ih (start + 1) (x + d))
      · exact le_rfl

private lemma sum_gaussianBoxPath_zero_of_mem
    {R : ℕ} {x : ℤ} (hx : x ∈ gaussianBox R)
    (f : GaussianBoxPath R 0 x → ℝ) :
    (∑ p, f p) = f ⟨(), hx⟩ := by
  let : Unique (GaussianBoxPath R 0 x) := {
    default := ⟨(), hx⟩
    uniq := fun p ↦ by
      change p = (⟨(), hx⟩ : {u : Unit // x ∈ gaussianBox R})
      apply Subtype.ext
      cases p.1
      rfl }
  exact Fintype.sum_unique f

private lemma sum_gaussianBoxPath_zero_of_not_mem
    {R : ℕ} {x : ℤ} (hx : x ∉ gaussianBox R)
    (f : GaussianBoxPath R 0 x → ℝ) :
    (∑ p, f p) = 0 := by
  let : IsEmpty (GaussianBoxPath R 0 x) := {
    false := fun p ↦ hx p.2 }
  exact Fintype.sum_empty f

lemma sum_gaussianBoxPath_succ_of_mem
    {R steps : ℕ} {x : ℤ} (hx : x ∈ gaussianBox R)
    (f : GaussianBoxPath R (steps + 1) x → ℝ) :
    (∑ p, f p) =
      ∑ d : ↥(gaussianBox R),
        ∑ q : GaussianBoxPath R steps (x + d.1),
          f (⟨(), hx⟩, ⟨d, q⟩) := by
  let e : GaussianBoxPath R (steps + 1) x ≃
      Σ d : ↥(gaussianBox R), GaussianBoxPath R steps (x + d.1) := {
    toFun p := p.2
    invFun z := (⟨(), hx⟩, z)
    left_inv p := by
      rcases p with ⟨px, z⟩
      have hp : px = (⟨(), hx⟩ : {u : Unit // x ∈ gaussianBox R}) :=
        Subsingleton.elim _ _
      subst px
      rfl
    right_inv z := rfl }
  calc
    (∑ p, f p) = ∑ z, f (e.symm z) :=
      Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = ∑ d : ↥(gaussianBox R),
        ∑ q : GaussianBoxPath R steps (x + d.1),
          f (⟨(), hx⟩, ⟨d, q⟩) := by
      rw [Fintype.sum_sigma]
      rfl

lemma sum_gaussianBoxPath_succ_of_not_mem
    {R steps : ℕ} {x : ℤ} (hx : x ∉ gaussianBox R)
    (f : GaussianBoxPath R (steps + 1) x → ℝ) :
    (∑ p, f p) = 0 := by
  let : IsEmpty (GaussianBoxPath R (steps + 1) x) := {
    false := fun p ↦ hx p.1.2 }
  exact Fintype.sum_empty f

/-- The recursive certified block partition is exactly the finite sum over
its killed Gaussian paths. -/
theorem certifiedProfileBlockPartition_eq_sum_paths
    (start steps R : ℕ) (x : ℤ) :
    certifiedProfileBlockPartition start steps R x =
      ∑ p : GaussianBoxPath R steps x,
        gaussianBoxPathCertifiedWeight start p := by
  induction steps generalizing start x with
  | zero =>
      by_cases hx : x ∈ gaussianBox R
      · rw [certifiedProfileBlockPartition, if_pos hx,
          sum_gaussianBoxPath_zero_of_mem hx]
        rfl
      · rw [certifiedProfileBlockPartition, if_neg hx,
          sum_gaussianBoxPath_zero_of_not_mem hx]
  | succ steps ih =>
      by_cases hx : x ∈ gaussianBox R
      · rw [certifiedProfileBlockPartition, if_pos hx,
          sum_gaussianBoxPath_succ_of_mem hx]
        simp only [gaussianBoxPathCertifiedWeight]
        simp_rw [ih]
        simp_rw [Finset.mul_sum]
        simpa using (gaussianBox R).sum_subtype
          (p := fun d : ℤ ↦ d ∈ gaussianBox R) (F := inferInstance) (by simp)
          (fun d ↦ ∑ q : GaussianBoxPath R steps (x + d),
            certifiedTaylorEdge (centeredProfileValue start x)
              (centeredProfileValue (start + 1) (x + d)) *
                gaussianBoxPathCertifiedWeight (start + 1) q)
      · rw [certifiedProfileBlockPartition, if_neg hx,
          sum_gaussianBoxPath_succ_of_not_mem hx]

/-- Exact logarithmic cost of comparing one fixed lattice Gaussian edge with
the corresponding certified Taylor edge.  The maximum makes the cost
nonnegative even when the certified edge is already larger. -/
def gaussianToCertifiedPointCost (l : ℕ) (x d : ℤ) : ℝ :=
  max 0 (Real.log
    (gaussianStepWeight l d /
      certifiedTaylorEdge
        (centeredProfileValue l x)
        (centeredProfileValue (l + 1) (x + d))))

lemma gaussianToCertifiedPointCost_nonneg (l : ℕ) (x d : ℤ) :
    0 ≤ gaussianToCertifiedPointCost l x d := by
  exact le_max_left _ _

/-- A completely explicit, finite uniform random-variance/Taylor comparison
cost at one level. -/
def finiteGaussianToCertifiedError (R l : ℕ) : ℝ :=
  ∑ x ∈ gaussianBox R, ∑ d ∈ gaussianBox R,
    gaussianToCertifiedPointCost l x d

lemma finiteGaussianToCertifiedError_nonneg (R l : ℕ) :
    0 ≤ finiteGaussianToCertifiedError R l := by
  exact Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun d _ ↦
    gaussianToCertifiedPointCost_nonneg l x d

private lemma exp_neg_max_log_ratio_mul_le {g c : ℝ}
    (hg : 0 ≤ g) (hc : 0 < c) :
    Real.exp (-max 0 (Real.log (g / c))) * g ≤ c := by
  by_cases hg0 : g = 0
  · subst g
    simp only [mul_zero]
    exact hc.le
  · have hgpos : 0 < g := lt_of_le_of_ne hg (Ne.symm hg0)
    have hlog : Real.log (g / c) ≤ max 0 (Real.log (g / c)) :=
      le_max_right _ _
    have hexp : Real.exp (-max 0 (Real.log (g / c))) ≤
        Real.exp (-Real.log (g / c)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hlog)
    calc
      Real.exp (-max 0 (Real.log (g / c))) * g ≤
          Real.exp (-Real.log (g / c)) * g :=
        mul_le_mul_of_nonneg_right hexp hg
      _ = c := by
        rw [Real.exp_neg, Real.exp_log (div_pos hgpos hc)]
        field_simp

lemma pointCost_gaussianStepWeight_le_certifiedTaylorEdge
    (l : ℕ) (x d : ℤ) :
    Real.exp (-gaussianToCertifiedPointCost l x d) * gaussianStepWeight l d ≤
      certifiedTaylorEdge
        (centeredProfileValue l x)
        (centeredProfileValue (l + 1) (x + d)) := by
  exact exp_neg_max_log_ratio_mul_le (gaussianStepWeight_nonneg l d)
    (certifiedTaylorEdge_pos _ _)

lemma pointCost_le_finiteGaussianToCertifiedError {R l : ℕ} {x d : ℤ}
    (hx : x ∈ gaussianBox R) (hd : d ∈ gaussianBox R) :
    gaussianToCertifiedPointCost l x d ≤ finiteGaussianToCertifiedError R l := by
  have hinner : gaussianToCertifiedPointCost l x d ≤
      ∑ e ∈ gaussianBox R, gaussianToCertifiedPointCost l x e := by
    exact Finset.single_le_sum
      (fun e he ↦ gaussianToCertifiedPointCost_nonneg l x e) hd
  have houter :
      (∑ e ∈ gaussianBox R, gaussianToCertifiedPointCost l x e) ≤
        ∑ y ∈ gaussianBox R, ∑ e ∈ gaussianBox R,
          gaussianToCertifiedPointCost l y e := by
    exact Finset.single_le_sum
      (fun y hy ↦ Finset.sum_nonneg fun e he ↦
        gaussianToCertifiedPointCost_nonneg l y e) hx
  exact hinner.trans houter

/-- The finite error sum gives the local comparison required by the recursive
reindexing theorem, with no analytic assumption. -/
theorem finiteError_gaussianStepWeight_le_certifiedTaylorEdge
    {R l : ℕ} {x d : ℤ} (hx : x ∈ gaussianBox R)
    (hd : d ∈ gaussianBox R) :
    Real.exp (-finiteGaussianToCertifiedError R l) * gaussianStepWeight l d ≤
      certifiedTaylorEdge
        (centeredProfileValue l x)
        (centeredProfileValue (l + 1) (x + d)) := by
  have hcost := pointCost_le_finiteGaussianToCertifiedError (l := l) hx hd
  calc
    Real.exp (-finiteGaussianToCertifiedError R l) * gaussianStepWeight l d ≤
        Real.exp (-gaussianToCertifiedPointCost l x d) *
          gaussianStepWeight l d := by
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hcost))
        (gaussianStepWeight_nonneg l d)
    _ ≤ certifiedTaylorEdge
          (centeredProfileValue l x)
          (centeredProfileValue (l + 1) (x + d)) :=
      pointCost_gaussianStepWeight_le_certifiedTaylorEdge l x d

/-- **Finite Gaussian-to-profile reindexing.**

Suppose the certified profile edge at every permitted deviation step is at
least its fixed Gaussian edge times `exp (-edgeError l)`.  Then the complete
finite constrained profile block is at least the Gaussian box partition
times the exponential of the sum of those edge errors.

This theorem closes all finite path reindexing and summation.  Its sole
hypothesis `hedge` is pointwise and is precisely the remaining
random-variance/Stirling-to-Gaussian comparison. -/
theorem exp_neg_blockErrorSum_mul_gaussianBoxPartition_le
    (edgeError : ℕ → ℝ) {start steps R : ℕ}
    (hedge : ∀ (l : ℕ) (x d : ℤ),
      x ∈ gaussianBox R → d ∈ gaussianBox R →
      Real.exp (-edgeError l) * gaussianStepWeight l d ≤
        certifiedTaylorEdge
          (centeredProfileValue l x)
          (centeredProfileValue (l + 1) (x + d)))
    (x : ℤ) :
    Real.exp (-blockErrorSum edgeError start steps) *
        gaussianBoxPartition start steps R x ≤
      certifiedProfileBlockPartition start steps R x := by
  induction steps generalizing start x with
  | zero =>
      simp only [blockErrorSum_zero, neg_zero, Real.exp_zero, one_mul,
        gaussianBoxPartition, certifiedProfileBlockPartition]
      exact le_rfl
  | succ steps ih =>
      by_cases hx : x ∈ gaussianBox R
      · simp only [blockErrorSum_succ, gaussianBoxPartition,
          certifiedProfileBlockPartition, if_pos hx]
        rw [neg_add, Real.exp_add, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d hd
        have htail := ih (start := start + 1) (x := x + d)
        have hedge' := hedge start x d hx hd
        have hgauss : 0 ≤ gaussianStepWeight start d :=
          gaussianStepWeight_nonneg start d
        have htailGauss : 0 ≤
            Real.exp (-blockErrorSum edgeError (start + 1) steps) *
              gaussianBoxPartition (start + 1) steps R (x + d) :=
          mul_nonneg (Real.exp_nonneg _)
            (gaussianBoxPartition_nonneg _ _ _ _)
        have hedgeNonneg : 0 ≤ certifiedTaylorEdge
            (centeredProfileValue start x)
            (centeredProfileValue (start + 1) (x + d)) :=
          certifiedTaylorEdge_nonneg _ _
        calc
          (Real.exp (-edgeError start) *
                Real.exp (-blockErrorSum edgeError (start + 1) steps)) *
              (gaussianStepWeight start d *
                gaussianBoxPartition (start + 1) steps R (x + d)) =
              (Real.exp (-edgeError start) * gaussianStepWeight start d) *
                (Real.exp (-blockErrorSum edgeError (start + 1) steps) *
                  gaussianBoxPartition (start + 1) steps R (x + d)) := by ring
          _ ≤ certifiedTaylorEdge
                (centeredProfileValue start x)
                (centeredProfileValue (start + 1) (x + d)) *
              (Real.exp (-blockErrorSum edgeError (start + 1) steps) *
                gaussianBoxPartition (start + 1) steps R (x + d)) :=
            mul_le_mul_of_nonneg_right hedge' htailGauss
          _ ≤ certifiedTaylorEdge
                (centeredProfileValue start x)
                (centeredProfileValue (start + 1) (x + d)) *
              certifiedProfileBlockPartition (start + 1) steps R (x + d) :=
            mul_le_mul_of_nonneg_left htail hedgeNonneg
      · simp only [gaussianBoxPartition, certifiedProfileBlockPartition,
          if_neg hx, mul_zero]
        exact le_rfl

/-- The Gaussian small-ball exponent and the complete finite profile
reindexing, assembled in one inequality. -/
theorem exp_totalError_le_certifiedProfileBlockPartition
    (edgeError : ℕ → ℝ) {start steps n R : ℕ}
    (hstart : 0 < start) (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2)
    (hedge : ∀ (l : ℕ) (x d : ℤ),
      x ∈ gaussianBox R → d ∈ gaussianBox R →
      Real.exp (-edgeError l) * gaussianStepWeight l d ≤
        certifiedTaylorEdge
          (centeredProfileValue l x)
          (centeredProfileValue (l + 1) (x + d))) :
    Real.exp
        (-(blockErrorSum edgeError start steps +
          1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2)) ≤
      certifiedProfileBlockPartition start steps R 0 := by
  have hgauss := gaussianBoxPartition_ge_exp hstart hbound hscale
  have hbridge := exp_neg_blockErrorSum_mul_gaussianBoxPartition_le
    edgeError (start := start) (steps := steps) hedge (0 : ℤ)
  calc
    Real.exp
        (-(blockErrorSum edgeError start steps +
          1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2)) =
        Real.exp (-blockErrorSum edgeError start steps) *
          Real.exp
            (-(1280 : ℝ) * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2) := by
      rw [neg_add, Real.exp_add]
      congr 2 <;> ring
    _ ≤ Real.exp (-blockErrorSum edgeError start steps) *
          gaussianBoxPartition start steps R 0 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      convert hgauss using 1 <;> ring
    _ ≤ certifiedProfileBlockPartition start steps R 0 := hbridge

/-- Assumption-free finite form of the HLOZ Gaussian/profile block lower
bound.  The first term in the exponent is the exact finite
Stirling/random-variance comparison cost; the second is the explicit spectral
small-ball cost. -/
theorem exp_explicitTotalError_le_certifiedProfileBlockPartition
    {start steps n R : ℕ} (hstart : 0 < start)
    (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2) :
    Real.exp
        (-(blockErrorSum (finiteGaussianToCertifiedError R) start steps +
          1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2)) ≤
      certifiedProfileBlockPartition start steps R 0 := by
  exact exp_totalError_le_certifiedProfileBlockPartition
    (finiteGaussianToCertifiedError R) hstart hbound hscale
      (fun _ _ _ hx hd ↦
        finiteError_gaussianStepWeight_le_certifiedTaylorEdge hx hd)

/-! ## From the late block to the complete constrained profile sum -/

/-- Exact finite logarithmic cost of comparing the certified weight of a
late Gaussian block path with the certified Taylor product of the complete
profile obtained by filling its prefix with the parabolic center. -/
def gaussianPathToFullProfileCost {start steps R : ℕ} (hstart : 2 ≤ start)
    (p : GaussianBoxPath R steps 0) : ℝ :=
  max 0 (Real.log
    (gaussianBoxPathCertifiedWeight start p /
      certifiedTaylorProduct
        (profileList (embeddedGaussianPathProfile hstart p))))

lemma gaussianPathToFullProfileCost_nonneg {start steps R : ℕ}
    (hstart : 2 ≤ start) (p : GaussianBoxPath R steps 0) :
    0 ≤ gaussianPathToFullProfileCost hstart p := by
  exact le_max_left _ _

/-- A finite, completely explicit prefix-completion cost.  Summing the
pointwise logarithmic costs avoids any loss of injectivity or any hidden
lower bound on the centered prefix product. -/
def finiteGaussianPathToFullProfileError {start steps R : ℕ}
    (hstart : 2 ≤ start) : ℝ :=
  ∑ p : GaussianBoxPath R steps 0,
    gaussianPathToFullProfileCost hstart p

lemma finiteGaussianPathToFullProfileError_nonneg {start steps R : ℕ}
    (hstart : 2 ≤ start) :
    0 ≤ finiteGaussianPathToFullProfileError
      (start := start) (steps := steps) (R := R) hstart := by
  exact Finset.sum_nonneg fun p _ ↦
    gaussianPathToFullProfileCost_nonneg hstart p

lemma pathCost_certifiedWeight_le_fullProfileProduct
    {start steps R : ℕ} (hstart : 2 ≤ start)
    (p : GaussianBoxPath R steps 0) :
    Real.exp (-gaussianPathToFullProfileCost hstart p) *
        gaussianBoxPathCertifiedWeight start p ≤
      certifiedTaylorProduct
        (profileList (embeddedGaussianPathProfile hstart p)) := by
  apply exp_neg_max_log_ratio_mul_le
  · rw [gaussianBoxPathCertifiedWeight_eq_product]
    exact certifiedTaylorProduct_nonneg _
  · exact certifiedTaylorProduct_pos _

lemma pathCost_le_finiteGaussianPathToFullProfileError
    {start steps R : ℕ} (hstart : 2 ≤ start)
    (p : GaussianBoxPath R steps 0) :
    gaussianPathToFullProfileCost hstart p ≤
      finiteGaussianPathToFullProfileError
        (start := start) (steps := steps) (R := R) hstart := by
  exact Finset.single_le_sum
    (fun q _ ↦ gaussianPathToFullProfileCost_nonneg hstart q)
    (Finset.mem_univ p)

lemma globalError_certifiedWeight_le_fullProfileProduct
    {start steps R : ℕ} (hstart : 2 ≤ start)
    (p : GaussianBoxPath R steps 0) :
    Real.exp
          (-finiteGaussianPathToFullProfileError
            (start := start) (steps := steps) (R := R) hstart) *
        gaussianBoxPathCertifiedWeight start p ≤
      certifiedTaylorProduct
        (profileList (embeddedGaussianPathProfile hstart p)) := by
  have hcost := pathCost_le_finiteGaussianPathToFullProfileError hstart p
  calc
    Real.exp
          (-finiteGaussianPathToFullProfileError
            (start := start) (steps := steps) (R := R) hstart) *
        gaussianBoxPathCertifiedWeight start p ≤
        Real.exp (-gaussianPathToFullProfileCost hstart p) *
          gaussianBoxPathCertifiedWeight start p := by
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hcost))
        (by
          rw [gaussianBoxPathCertifiedWeight_eq_product]
          exact certifiedTaylorProduct_nonneg _)
    _ ≤ certifiedTaylorProduct
          (profileList (embeddedGaussianPathProfile hstart p)) :=
      pathCost_certifiedWeight_le_fullProfileProduct hstart p

/-- The complete finite reindexing theorem.  Every Gaussian block path is
embedded injectively into the actual global constrained profile finset.  The
only hypotheses are deterministic window conditions ensuring that the
chosen integer deviations lie in the HLOZ profile window. -/
theorem exp_neg_fullProfileError_mul_certifiedProfileBlockPartition_le
    {start steps R : ℕ} (hstart : 2 ≤ start) {delta : ℝ}
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    Real.exp
          (-finiteGaussianPathToFullProfileError
            (start := start) (steps := steps) (R := R) hstart) *
        certifiedProfileBlockPartition start steps R 0 ≤
      constrainedTaylorGaussianWeight (start + steps) delta := by
  let e : GaussianBoxPath R steps 0 → Profile (start + steps) :=
    embeddedGaussianPathProfile hstart
  have he : Function.Injective e :=
    embeddedGaussianPathProfile_injective hstart hcenter
  have himage : Finset.image e Finset.univ ⊆
      constrainedProfiles (start + steps) delta := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨p, _hp, rfl⟩ := hm
    exact embeddedGaussianPathProfile_mem_constrainedProfiles
      hstart p hcenter hwidth
  rw [certifiedProfileBlockPartition_eq_sum_paths, Finset.mul_sum]
  calc
    (∑ p : GaussianBoxPath R steps 0,
        Real.exp
            (-finiteGaussianPathToFullProfileError
              (start := start) (steps := steps) (R := R) hstart) *
          gaussianBoxPathCertifiedWeight start p) ≤
        ∑ p : GaussianBoxPath R steps 0,
          certifiedTaylorProduct (profileList (e p)) := by
      exact Finset.sum_le_sum fun p _ ↦
        globalError_certifiedWeight_le_fullProfileProduct hstart p
    _ = ∑ m ∈ Finset.image e Finset.univ,
          certifiedTaylorProduct (profileList m) := by
      symm
      exact Finset.sum_image he.injOn
    _ ≤ ∑ m ∈ constrainedProfiles (start + steps) delta,
          certifiedTaylorProduct (profileList m) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun m _ _ ↦ certifiedTaylorProduct_nonneg (profileList m))
    _ = constrainedTaylorGaussianWeight (start + steps) delta := rfl

/-- Assumption-free finite HLOZ constrained-profile lower bound.  Its exact
exponent is the sum of:

* the finite prefix-completion log-ratio cost;
* the finite local Gaussian-to-certified-Taylor edge costs; and
* the spectral small-ball cost `1280 * steps * n^2 / R^2`.
-/
theorem exp_completeProfileError_le_constrainedTaylorGaussianWeight
    {start steps n R : ℕ} (hstart : 2 ≤ start)
    (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2)
    {delta : ℝ}
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    Real.exp
        (-(finiteGaussianPathToFullProfileError
              (start := start) (steps := steps) (R := R) hstart +
            blockErrorSum (finiteGaussianToCertifiedError R) start steps +
            1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2)) ≤
      constrainedTaylorGaussianWeight (start + steps) delta := by
  have hblock := exp_explicitTotalError_le_certifiedProfileBlockPartition
    (start := start) (steps := steps) (n := n) (R := R)
    (by omega) hbound hscale
  have hglobal :=
    exp_neg_fullProfileError_mul_certifiedProfileBlockPartition_le
      hstart hcenter hwidth
  calc
    Real.exp
        (-(finiteGaussianPathToFullProfileError
              (start := start) (steps := steps) (R := R) hstart +
            blockErrorSum (finiteGaussianToCertifiedError R) start steps +
            1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2)) =
        Real.exp
          (-finiteGaussianPathToFullProfileError
            (start := start) (steps := steps) (R := R) hstart) *
          Real.exp
            (-(blockErrorSum (finiteGaussianToCertifiedError R) start steps +
              1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp
          (-finiteGaussianPathToFullProfileError
            (start := start) (steps := steps) (R := R) hstart) *
          certifiedProfileBlockPartition start steps R 0 := by
      exact mul_le_mul_of_nonneg_left hblock (Real.exp_nonneg _)
    _ ≤ constrainedTaylorGaussianWeight (start + steps) delta := hglobal

/-- The same explicit finite lower bound for the exact negative-binomial
constrained-profile weight. -/
theorem exp_completeProfileError_le_constrainedProfileWeight
    {start steps n R : ℕ} (hstart : 2 ≤ start)
    (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2)
    {delta : ℝ} (hdelta : delta ≤ 1)
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    Real.exp
        (-(finiteGaussianPathToFullProfileError
              (start := start) (steps := steps) (R := R) hstart +
            blockErrorSum (finiteGaussianToCertifiedError R) start steps +
            1280 * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2)) ≤
      constrainedProfileWeight (start + steps) delta := by
  exact (exp_completeProfileError_le_constrainedTaylorGaussianWeight
    hstart hbound hscale hcenter hwidth).trans
      (constrainedTaylorGaussianWeight_le_constrainedProfileWeight
        (start + steps) hdelta)

end

end Erdos1165.GaussianProfileReindex
