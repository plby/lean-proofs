module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Cases

/-!
## Continuous multilinear map constructors

We define continuous multilinear maps for

1. `fstCmmap` for `fst`
2. `sndCmmap` for `snd`
3. `smulCmmap` for two continuous multilinear maps `smul`'ed together
4. Products of monomials: `termCmmap` for `x^a * y^b`
5. `conjCLM` for `conj` (this is one a continuous linear map)
6. `cmmapApplyCmap`, a continuous linear map that evaluates a continuous multilinear map at a point
-/

open scoped ComplexConjugate
noncomputable section

variable {n : ℕ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {ι : Type}
variable {R A B E : Type} [Semiring R]

theorem ContinuousMultilinearMap.toFun_eq_coe {R A B : Type} [Semiring R] [AddCommMonoid A]
    [Module R A] [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B]
    (f : ContinuousMultilinearMap R (fun _ : Fin n ↦ A) B) : f.toFun = ⇑f := by
  rw [MultilinearMap.toFun_eq_coe]; simp

/-- `fst` as a `ContinuousMultilinearMap` -/
def fstCmmap (R : Type) (A B : Type) [Semiring R] [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B] :
    ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A × B) A :=
  ContinuousMultilinearMap.ofSubsingleton R (A × B) A (0 : Fin 1) (ContinuousLinearMap.fst R A B)

/-- `snd` as a `ContinuousMultilinearMap` -/
def sndCmmap (R : Type) (A B : Type) [Semiring R] [AddCommMonoid A] [Module R A]
    [TopologicalSpace A] [AddCommMonoid B] [Module R B] [TopologicalSpace B] :
    ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A × B) B :=
  ContinuousMultilinearMap.ofSubsingleton R (A × B) B (0 : Fin 1) (ContinuousLinearMap.snd R A B)

theorem fstCmmap_apply [AddCommMonoid A] [Module R A] [TopologicalSpace A] [AddCommMonoid B]
    [Module R B] [TopologicalSpace B] (a : A) (b : B) : (fstCmmap R A B fun _ ↦ (a, b)) = a := by
  simp only [fstCmmap, ContinuousMultilinearMap.ofSubsingleton_apply_apply,
    ContinuousLinearMap.coe_fst']

theorem sndCmmap_apply [AddCommMonoid A] [Module R A] [TopologicalSpace A] [AddCommMonoid B]
    [Module R B] [TopologicalSpace B] (a : A) (b : B) : (sndCmmap R A B fun _ ↦ (a, b)) = b := by
  simp only [sndCmmap, ContinuousMultilinearMap.ofSubsingleton_apply_apply,
    ContinuousLinearMap.coe_snd']

theorem fstCmmap_norm [NormedRing A] [NormedAlgebra 𝕜 A] [NormOneClass A] [NormedRing B]
    [NormedAlgebra 𝕜 B] [NormOneClass B] : ‖fstCmmap 𝕜 A B‖ = 1 := by
  apply le_antisymm
  · refine (fstCmmap 𝕜 A B).opNorm_le_bound (M := 1) (by norm_num) ?_
    intro z; simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, one_mul]
    have e : z = (fun _ ↦ ((z 0).1, (z 0).2)) := by apply funext; intro i; rw [Fin.eq_zero i]
    rw [e]
    rw [fstCmmap_apply]; simp only [Fin.isValue, Prod.mk.eta, ge_iff_le]; exact norm_fst_le (z 0)
  · have lo := (fstCmmap 𝕜 A B).unit_le_opNorm (m := fun _ ↦ (1, 1)) ?_
    rw [fstCmmap_apply, norm_one] at lo; assumption
    rw [pi_norm_le_iff_of_nonneg]; intro i; simp only [Prod.norm_def, norm_one]
    repeat norm_num

theorem sndCmmap_norm [NormedRing A] [NormedAlgebra 𝕜 A] [NormOneClass A] [NormedRing B]
    [NormedAlgebra 𝕜 B] [NormOneClass B] : ‖sndCmmap 𝕜 A B‖ = 1 := by
  apply le_antisymm
  · apply (sndCmmap 𝕜 A B).opNorm_le_bound (M := 1) (by norm_num)
    intro z; simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, one_mul]
    have e : z = (fun _ ↦ ((z 0).1, (z 0).2)) := by apply funext; intro i; rw [Fin.eq_zero i]
    rw [e]
    rw [sndCmmap_apply]; simp only [Fin.isValue, Prod.mk.eta, ge_iff_le]; exact norm_snd_le (z 0)
  · have lo := (sndCmmap 𝕜 A B).unit_le_opNorm (m := fun _ ↦ (1, 1)) ?_
    rw [sndCmmap_apply, norm_one] at lo; assumption
    rw [pi_norm_le_iff_of_nonneg]; intro i; simp only [Prod.norm_def, norm_one]
    repeat norm_num

-- Lemmas for `smulCmmap`
theorem update_0_0 (z : Fin (n + 1) → A) (x : A) :
    Function.update (fun _ : Fin 1 ↦ z 0) 0 x = (fun _ : Fin 1 ↦ x) := by
  apply funext; intro i
  have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton]
  rw [i0]; simp only [Function.update_self]

theorem update_0_succ (d : DecidableEq (Fin (n + 1))) (f : Fin (n + 1) → A) (x : A) (i : Fin n) :
    @Function.update _ _ d f 0 x i.succ = f i.succ := by
  rw [Function.update_apply]; simp only [ite_eq_right_iff]
  have i0 := Fin.succ_ne_zero i
  intro h; exfalso; exact i0 h

theorem update_nz_0 (d : DecidableEq (Fin (n + 1))) (f : Fin (n + 1) → A) {x : A} {i : Fin (n + 1)}
    (i0 : i ≠ 0) : @Function.update _ _ d f i x 0 = f 0 := by rw [Function.update_of_ne i0.symm]

theorem update_nz_succ (d : DecidableEq (Fin (n + 1))) (f : Fin (n + 1) → A) (x : A)
    {i : Fin (n + 1)} (i0 : i ≠ 0) :
    (fun j : Fin n ↦ @Function.update _ _ d f i x j.succ) =
      Function.update (fun j : Fin n ↦ f j.succ) (i.pred i0) x := by
  apply funext; intro k
  by_cases ki : k.succ = i
  · have ki' : k = i.pred i0 := by simp_rw [← ki, Fin.pred_succ]
    rw [ki, ki']; rw [Function.update_self]; rw [Function.update_self]
  · rw [Function.update_of_ne ki]
    rw [Function.update_of_ne _]
    by_contra h
    simp only [h, Fin.succ_pred, not_true_eq_false] at ki

/-- Raw cons of two continuous multilinear maps -/
def smulCmmapFn [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) : (∀ _ : Fin (n + 1), A) → B :=
  fun z ↦ (x.toFun (fun _ ↦ z 0)) • xs.toFun (fun i ↦ z i.succ)

/-- `smulCmmapFn` is multiadditive -/
theorem smul_cmmap_add [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ∀ (d : DecidableEq (Fin (n + 1))) (z : ∀ _ : Fin (n + 1), A) (i : Fin (n + 1)) (u v : A),
      smulCmmapFn x xs (@Function.update _ _ d z i (u + v)) =
        smulCmmapFn x xs (@Function.update _ _ d z i u) +
          smulCmmapFn x xs (@Function.update _ _ d z i v) := by
  intro d z i u v
  by_cases i0 : i = 0
  · rw [i0]
    have uv := x.map_update_add (fun _ ↦ z 0) 0 u v
    simp only [update_0_0 z _] at uv
    simp only [Function.update_self, MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      uv, add_smul, smulCmmapFn, update_0_succ]
  · simp only [smul_add, update_nz_0 d z i0, MultilinearMap.toFun_eq_coe,
    ContinuousMultilinearMap.coe_coe, update_nz_succ d z _ i0, MultilinearMap.map_update_add,
    smul_add, smulCmmapFn]

/-- `smulCmmapFn` commutes with scalars -/
theorem smul_cmmap_smul [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ∀ (d : DecidableEq (Fin (n + 1))) (z : ∀ _ : Fin (n + 1), A) (i : Fin (n + 1)) (s : 𝕜) (u : A),
      smulCmmapFn x xs (@Function.update _ _ d z i (s • u)) =
        s • smulCmmapFn x xs (@Function.update _ _ d z i u) := by
  intro d z i s u
  rw [smulCmmapFn]
  by_cases i0 : i = 0
  · rw [i0]
    have su := x.map_update_smul (fun _ ↦ z 0) 0 s u
    rw [update_0_0 z _, update_0_0 z _] at su
    simp only [Function.update_self, MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      su, smul_eq_mul, update_0_succ d z _ _, smulCmmapFn, ← smul_assoc]
  · have su := xs.map_update_smul (fun j ↦ z j.succ) (i.pred i0) s u
    simp only [MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe, update_nz_0 d z i0,
      update_nz_succ d z _ i0, su, smul_comm _ s, smulCmmapFn]

/-- `smulCmmapFn` is continuous -/
theorem smul_cmmap_cont [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) : Continuous (smulCmmapFn x xs) := by
  apply Continuous.smul; repeat continuity

/-- Cons two `ContinuousMultilinearMap`s together, combining values via `•` -/
def smulCmmap (𝕜 A B : Type) [NontriviallyNormedField 𝕜] [AddCommMonoid A] [Module 𝕜 A]
    [TopologicalSpace A] [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) B where
  toFun := smulCmmapFn x xs
  map_update_add' := smul_cmmap_add x xs _
  map_update_smul' := smul_cmmap_smul x xs _
  cont := smul_cmmap_cont x xs

theorem smulCmmap_apply [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) (z : ∀ _ : Fin (n + 1), A) :
    smulCmmap _ _ _ x xs z = (x fun _ ↦ z 0) • xs fun i ↦ z i.succ := by
  rw [smulCmmap, ←ContinuousMultilinearMap.toFun_eq_coe]; simp only; rfl

theorem smulCmmap_norm [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 B] (x : ContinuousMultilinearMap 𝕜 (fun _ : Fin 1 ↦ A) 𝕜)
    (xs : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ A) B) :
    ‖smulCmmap 𝕜 A B x xs‖ ≤ ‖x‖ * ‖xs‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound; bound
  intro z; rw [smulCmmap_apply]
  have xb := ContinuousMultilinearMap.le_opNorm x fun _ : Fin 1 ↦ z 0
  have xsb := ContinuousMultilinearMap.le_opNorm xs fun i : Fin n ↦ z i.succ
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_const, Finset.card_singleton,
    pow_one] at xb xsb
  have e0 := Fin.prod_cons ‖z 0‖ fun i : Fin n ↦ ‖z i.succ‖
  have e1 : ‖z 0‖ = (fun i : Fin (n + 1) ↦ ‖z i‖) 0 := rfl
  have e2 : (fun i : Fin n ↦ ‖z i.succ‖) = Fin.tail fun i : Fin (n + 1) ↦ ‖z i‖ := rfl
  nth_rw 1 [e1] at e0; nth_rw 1 [e2] at e0; rw [Fin.cons_self_tail (fun i ↦ ‖z i‖)] at e0
  calc ‖(x fun _ : Fin 1 ↦ z 0) • xs fun i : Fin n ↦ z i.succ‖
    _ ≤ ‖x‖ * ‖z 0‖ * (‖xs‖ * Finset.univ.prod fun i : Fin n ↦ ‖z i.succ‖) := by
      rw [norm_smul]; bound
    _ = ‖x‖ * ‖xs‖ * (‖z 0‖ * Finset.univ.prod fun i : Fin n ↦ ‖z i.succ‖) := by ring
    _ = ‖x‖ * ‖xs‖ * Finset.univ.prod fun i : Fin (n + 1) ↦ ‖z i‖ := by rw [←e0]

/-- A term of the general `n`-linear map on `𝕜 × 1𝕜,
    equal to `z0^k * z1^(n-k)` when applied to `fun _ ↦ (z0,z1)` -/
public noncomputable def termCmmap (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] : ∀ n : ℕ, ℕ → E → ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ 𝕜 × 𝕜) E
  | 0 => fun _ x ↦ ContinuousMultilinearMap.constOfIsEmpty _ _ x
  | n + 1 => fun k x ↦
    smulCmmap _ _ _ (if n < k then fstCmmap 𝕜 𝕜 𝕜 else sndCmmap 𝕜 𝕜 𝕜) (termCmmap 𝕜 n k x)

public theorem termCmmap_apply [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 𝕜 E]
    [IsScalarTower 𝕜 𝕜 E] (n k : ℕ) (a b : 𝕜) (x : E) :
    (termCmmap 𝕜 n k x fun _ ↦ (a, b)) = a ^ min k n • b ^ (n - k) • x := by
  induction' n with n h
  · simp only [termCmmap, ContinuousMultilinearMap.constOfIsEmpty_apply, min_zero, pow_zero,
    zero_tsub, one_smul]
  · rw [termCmmap, smulCmmap_apply, h]
    by_cases nk : n < k
    · have nsk : n.succ ≤ k := Nat.succ_le_iff.mpr nk
      simp only [nk, if_true, fstCmmap_apply, min_eq_right nk.le, min_eq_right nsk,
        Nat.sub_eq_zero_of_le nk.le, Nat.sub_eq_zero_of_le nsk, pow_zero, one_smul, smul_smul,
        pow_succ']
    · simp [nk]; simp at nk
      rw [sndCmmap_apply]
      have nsk : k ≤ n.succ := Nat.le_succ_of_le nk
      rw [min_eq_left nk, min_eq_left nsk]
      rw [smul_comm b _, ← smul_assoc b _ _, smul_eq_mul, ← pow_succ', ← Nat.sub_add_comm nk]

public theorem termCmmap_norm (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (n k : ℕ) (x : E) : ‖termCmmap 𝕜 n k x‖ ≤ ‖x‖ := by
  induction' n with n nh
  · simp only [termCmmap, le_refl, ContinuousMultilinearMap.norm_constOfIsEmpty]
  · rw [termCmmap]; simp only
    generalize ht : termCmmap 𝕜 n k x = t; rw [ht] at nh
    have tn := smulCmmap_norm (if n < k then fstCmmap 𝕜 𝕜 𝕜 else sndCmmap 𝕜 𝕜 𝕜) t
    by_cases nk : n < k
    · simp only [if_pos nk] at tn ⊢
      rw [fstCmmap_norm] at tn
      simp only [one_mul] at tn
      exact _root_.trans tn nh
    · simp only [if_neg nk] at tn ⊢
      rw [sndCmmap_norm] at tn
      simp only [one_mul] at tn
      exact _root_.trans tn nh

/-- `conj` as a `ContinuousLinearMap`. This is `starₗᵢ ℂ`, but with a simpler type. -/
public def conjCLM : ℂ →L[ℝ] ℂ where
  toFun z := conj z
  map_add' := by simp only [map_add, forall_const]
  map_smul' := by simp only [Complex.real_smul, map_mul, RingHom.id_apply, Complex.conj_ofReal,
    implies_true]

public theorem conjCLM_apply (z : ℂ) : conjCLM z = conj z := by rfl

/-- The continuous linear map that evaluates a continuous multilinear map at a point -/
public def cmmapApplyCmap (𝕜 : Type) {I : Type} (A : I → Type) (B : Type) [Fintype I]
    [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace 𝕜 (A i)]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] (x : ∀ i, A i) : ContinuousMultilinearMap 𝕜 A B →L[𝕜] B
    where
  toFun f := f x
  map_add' := by simp
  map_smul' := by simp
  cont := by simp [continuous_eval_const]

@[simp] public theorem cmmapApplyCmap_apply {I : Type} (A : I → Type) (B : Type) [Fintype I]
    [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace 𝕜 (A i)]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] (x : ∀ i, A i) (f : ContinuousMultilinearMap 𝕜 A B) :
    cmmapApplyCmap 𝕜 A B x f = f x := by rfl

/-- Prove `A x = 0` by `x = 0` for a continuous linear map `A` -/
public lemma ContinuousLinearMap.apply_eq_zero_of_eq_zero {𝕜 X Y : Type} [NormedField 𝕜]
    [TopologicalSpace X] [NormedAddCommGroup X] [Module 𝕜 X] [NormedAddCommGroup Y] [Module 𝕜 Y]
    (f : X →L[𝕜] Y) {x : X} (h : x = 0) : f x = 0 := by
  rw [h, ContinuousLinearMap.map_zero]

/-- `.smulRight` is nonzero if it's inputs are -/
public lemma ContinuousLinearMap.smulRight_ne_zero {R A B : Type} [Ring R] [TopologicalSpace A]
    [AddCommMonoid A] [TopologicalSpace R] [Module R A] [TopologicalSpace B] [AddCommMonoid B]
    [Module R B] [ContinuousSMul R B] [NoZeroSMulDivisors R B] {c : A →L[R] R} {f : B}
    (c0 : c ≠ 0) (f0 : f ≠ 0) :
    c.smulRight f ≠ 0 := by
  rcases ContinuousLinearMap.exists_ne_zero c0 with ⟨x,cx⟩
  simp only [Ne, ContinuousLinearMap.ext_iff, not_forall, _root_.zero_apply,
    ContinuousLinearMap.smulRight_apply]
  exact ⟨x, fun h ↦ (eq_zero_or_eq_zero_of_smul_eq_zero h).elim cx f0⟩

/-- `1 ≠ 0`, `ContinuousLinearMap` case -/
public lemma ContinuousLinearMap.one_ne_zero {R A : Type} [Ring R] [TopologicalSpace A]
    [AddCommMonoid A] [Module R A] [Nontrivial A] : (1 : A →L[R] A) ≠ 0 := by
  simp only [Ne, ContinuousLinearMap.ext_iff, not_forall, _root_.zero_apply,
    _root_.one_apply_eq_self]
  apply exists_ne

/-- `mkPiRing` is continuous -/
public lemma ContinuousMultilinearMap.continuous_mkPiRing {𝕜 ι E : Type} [NontriviallyNormedField 𝕜]
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    Continuous (fun z : E ↦ ContinuousMultilinearMap.mkPiRing 𝕜 ι z) := by
  rw [Metric.continuous_iff]
  intro x e e0
  refine ⟨e / 2, by bound, fun y xy ↦ ?_⟩
  simp only [dist_eq_norm] at xy
  refine lt_of_le_of_lt (b := e / 2) ?_ (by bound)
  rw [dist_eq_norm, ContinuousMultilinearMap.opNorm_le_iff (by bound)]
  intro m
  simp only [_root_.sub_apply, ContinuousMultilinearMap.mkPiRing_apply,
    ← smul_sub]
  refine le_trans (norm_smul_le _ _) ?_
  rw [mul_comm]
  bound

/-!
### Conjugate a `ContinuousMultilinearMap` with complex `conj`
-/

/-- Conjugate a `ContinuousMultilinearMap` with complex `conj` -/
public def ContinuousMultilinearMap.conj_conj [Fintype ι]
    (m : ContinuousMultilinearMap ℂ (fun _ : ι ↦ ℂ) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : ι ↦ ℂ) ℂ where
  toFun := fun z ↦ conj (m fun i ↦ conj (z i))
  map_update_add' g a x y := by
    simp only [← map_add, Function.apply_update (fun _ z ↦ conj z) (g := g), ← m.map_update_add]
  map_update_smul' g a s y := by
    simp only [smul_eq_mul, Function.apply_update (fun _ z ↦ conj z) (g := g), map_mul]
    simp only [← smul_eq_mul, m.map_update_smul]
    simp only [smul_eq_mul, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  cont := by continuity

@[simp] public lemma ContinuousMultilinearMap.conj_conj_apply [Fintype ι]
    (m : ContinuousMultilinearMap ℂ (fun _ : ι ↦ ℂ) ℂ) (x : ι → ℂ) :
    m.conj_conj x = conj (m fun i ↦ conj (x i)) := by rfl
