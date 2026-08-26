/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.TailCharacters

namespace Erdos254

open Set MeasureTheory
open scoped BigOperators Topology

/-- An integral character of a finite-dimensional torus, in additive notation. -/
def torusCharacter {d : Type*} [Fintype d] (z : d → ℤ) :
    UnitAddTorus d →+ UnitAddCircle where
  toFun x := ∑ i, z i • x i
  map_zero' := by simp
  map_add' := by intro x y; simp [Finset.sum_add_distrib]

lemma continuous_torusCharacter {d : Type*} [Fintype d] (z : d → ℤ) :
    Continuous (torusCharacter z) := by
  change Continuous (fun x : UnitAddTorus d ↦ ∑ i, z i • x i)
  fun_prop

private lemma toCircle_sum {ι : Type*} (s : Finset ι) (f : ι → UnitAddCircle) :
    (∑ i ∈ s, f i).toCircle = ∏ i ∈ s, (f i).toCircle := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha, AddCircle.toCircle_add, ih]

lemma mFourier_eq_torusCharacter {d : Type*} [Fintype d] (z : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier z x = ((torusCharacter z x).toCircle : ℂ) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
    torusCharacter, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toCircle_sum]
  exact (map_prod Circle.coeHom (fun i ↦ (z i • x i).toCircle) Finset.univ).symm

lemma mFourier_apply_add {d : Type*} [Fintype d] (z : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier z (x + y) = UnitAddTorus.mFourier z x * UnitAddTorus.mFourier z y := by
  simp only [mFourier_eq_torusCharacter, map_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma mFourier_eq_one_iff {d : Type*} [Fintype d] (z : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier z x = 1 ↔ torusCharacter z x = 0 := by
  rw [mFourier_eq_torusCharacter]
  constructor
  · intro h
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
    apply Subtype.ext
    simpa only [AddCircle.toCircle_zero, Circle.coe_one] using h
  · intro h
    rw [h, AddCircle.toCircle_zero, Circle.coe_one]

/-- Integration of continuous functions after a continuous map from a compact
probability space is a continuous linear functional. -/
noncomputable def compactAverage {X K : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (v : K → X) (hv : Continuous v) : C(X, ℂ) →L[ℂ] ℂ := by
  have hint : ∀ φ : C(X, ℂ), Integrable (fun k ↦ φ (v k)) μ := by
    intro φ
    simpa only [integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ (φ.continuous.comp hv).continuousOn :
        IntegrableOn (fun k ↦ φ (v k)) univ μ)
  let T : C(X, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ ↦ ∫ k, φ (v k) ∂μ
      map_add' := fun φ ψ ↦ integral_add (hint φ) (hint ψ)
      map_smul' := fun c φ ↦ integral_smul c (fun k ↦ φ (v k)) }
  exact T.mkContinuous (μ.real univ) (fun φ ↦ by
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (fun k ↦ φ.norm_coe_le_norm (v k)))
    simpa only [T, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using h)

@[simp] lemma compactAverage_apply {X K : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (v : K → X) (hv : Continuous v) (φ : C(X, ℂ)) :
    compactAverage μ v hv φ = ∫ k, φ (v k) ∂μ := rfl

/-- Closed subgroups of a finite-dimensional torus are separated by integral
characters. The proof uses Haar averaging and Mathlib's Fourier density theorem,
not a closed-subgroup classification assumption. -/
theorem mem_of_torus_characters {d : Type*} [Fintype d]
    (H : AddSubgroup (UnitAddTorus d)) (hH : IsClosed (H : Set (UnitAddTorus d)))
    (x : UnitAddTorus d)
    (hx : ∀ z : d → ℤ, (∀ h ∈ H, torusCharacter z h = 0) → torusCharacter z x = 0) : x ∈ H := by
  classical
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let μ : Measure H := Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts H)
  have hμ : μ univ = 1 := by
    exact Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
  let : IsProbabilityMeasure μ := ⟨hμ⟩
  let T : UnitAddTorus d → C(UnitAddTorus d, ℂ) →L[ℂ] ℂ := fun a ↦
    compactAverage μ (fun h : H ↦ a + (h : UnitAddTorus d))
      (continuous_const.add continuous_subtype_val)
  have hm : ∀ z : d → ℤ, T x (UnitAddTorus.mFourier z) = T 0 (UnitAddTorus.mFourier z) := by
    intro z
    let I : ℂ := ∫ h : H, UnitAddTorus.mFourier z h ∂μ
    have hTx : T x (UnitAddTorus.mFourier z) = UnitAddTorus.mFourier z x * I := by
      simp only [T, compactAverage_apply, mFourier_apply_add, integral_const_mul, I]
    have hT0 : T 0 (UnitAddTorus.mFourier z) = I := by
      simp only [T, compactAverage_apply, zero_add, I]
    rw [hTx, hT0]
    by_cases hkill : ∀ h ∈ H, torusCharacter z h = 0
    · rw [(mFourier_eq_one_iff z x).mpr (hx z hkill), one_mul]
    · push Not at hkill
      obtain ⟨h, hh, hchar⟩ := hkill
      have hne : UnitAddTorus.mFourier z h ≠ 1 :=
        fun heq ↦ hchar ((mFourier_eq_one_iff z h).mp heq)
      have hInv := integral_add_left_eq_self (μ := μ)
        (fun t : H ↦ UnitAddTorus.mFourier z t) (⟨h, hh⟩ : H)
      have hmul : UnitAddTorus.mFourier z h * I = I := by
        simpa only [AddSubgroup.coe_add, mFourier_apply_add, integral_const_mul, I] using hInv
      have hz : (UnitAddTorus.mFourier z h - 1) * I = 0 := by
        rw [sub_mul, one_mul, hmul, sub_self]
      have hI : I = 0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
      rw [hI, mul_zero]
  have hdense : Dense (↑(Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d)))) :
      Set C(UnitAddTorus d, ℂ)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      UnitAddTorus.span_mFourier_closure_eq_top]
    rfl
  have hT : T x = T 0 := ContinuousLinearMap.ext_on hdense (by
    rintro φ ⟨z, rfl⟩
    exact hm z)
  by_contra hxH
  let S : Set (UnitAddTorus d) := (fun h : UnitAddTorus d ↦ x + h) '' (H : Set (UnitAddTorus d))
  have hS : IsClosed S := (hH.isCompact.image (continuous_const.add continuous_id)).isClosed
  have hdisj : Disjoint (H : Set (UnitAddTorus d)) S := by
    apply Set.disjoint_left.mpr
    rintro a ha ⟨h, hh, rfl⟩
    have := H.sub_mem ha hh
    exact hxH (by simpa only [add_sub_cancel_right] using this)
  obtain ⟨g, hg0, hg1, _⟩ := exists_continuous_zero_one_of_isClosed hH hS hdisj
  let φ : C(UnitAddTorus d, ℂ) := ⟨fun a ↦ (g a : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  have h0 : T 0 φ = 0 := by
    change (∫ h : H, (g (0 + (h : UnitAddTorus d)) : ℂ) ∂μ) = 0
    have heq : (fun h : H ↦ (g (0 + (h : UnitAddTorus d)) : ℂ)) = fun _ ↦ 0 := by
      funext h
      simp only [zero_add, hg0 h.2, Pi.zero_apply, Complex.ofReal_zero]
    rw [heq, integral_zero]
  have h1 : T x φ = 1 := by
    change (∫ h : H, (g (x + (h : UnitAddTorus d)) : ℂ) ∂μ) = 1
    have heq : (fun h : H ↦ (g (x + (h : UnitAddTorus d)) : ℂ)) = fun _ ↦ 1 := by
      funext h
      have hmem : x + (h : UnitAddTorus d) ∈ S := ⟨h, h.2, rfl⟩
      simp only [hg1 hmem, Pi.one_apply, Complex.ofReal_one]
    rw [heq]
    simp
  have heq := congrArg (fun L : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ ↦ L φ) hT
  rw [h0, h1] at heq
  exact one_ne_zero heq

/-- The all-phase form of Bergelson–Simmons Claim 2.14. Under the stronger
divergence hypothesis used by Fan, no nontrivial multiple of the generator is needed. -/
theorem generator_mem_tailSubgroup {d : Type*} [Fintype d]
    {A : Set ℕ} (hA : PhaseDivergent A) (θ : UnitAddTorus d) :
    θ ∈ tailSubgroup A (fun n ↦ n • θ) := by
  apply mem_of_torus_characters (tailSubgroup A (fun n ↦ n • θ))
    (isClosed_tailLimitSet A (fun n ↦ n • θ)) θ
  intro z hz
  exact character_eq_zero_of_annihilates_tail hA θ (torusCharacter z)
    (continuous_torusCharacter z) hz

end Erdos254
