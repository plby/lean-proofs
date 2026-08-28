import Wikipedia.HopfProblem.DegreeCollapseCompactNativeLevelSuspension
import Wikipedia.HopfProblem.DegreeCollapseNativeModelHeightDerivative
import Wikipedia.HopfProblem.DegreeCollapseNativeExteriorFlow

/-!
# Supported holonomy insertion across a whole native regular level

The actual cylinder is based on the native level manifold, with no
single-coordinate-chart requirement. Compact suspension gives a global
smooth field, its complete native flow, exact prescribed holonomy, and
unchanged exterior germs, zeros and strict descent for the original height.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z E N M : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace N] [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N] [T2Space N]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_native_whole_level_holonomy
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = univ)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ p, p.2 ∈ Ioo (0 : ℝ) 1 → f (A p) = b - s * p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ A.target, V x =
      VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField x)
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) V)
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞) {K S : Set N}
    (hK : IsCompact K) (I : SupportedRelativeIsotopy D K S) :
    ∃ (C : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M)
      (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
        (N × ℝ) (N × ℝ) ∞),
      IsCompact C ∧ C ⊆ A.target ∩ f ⁻¹' Ioo (b - s) b ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
      (∀ x, V' x = 0 ↔ V x = 0) ∧
      (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 → mvfderiv 𝓘(ℝ, E) f x (V' x) < 0) ∧
      (∀ x ∉ C, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
      (∀ x ∈ A.target, ∀ t, G t x ∈ A.target) ∧
      (∀ x ∉ A.target, ∀ t, G t x = H t x) ∧
      (∀ p t, G t (A p) = A (nativeSuspensionFlow Ψ t p)) ∧
      (∀ x, G 1 (A (x, 0)) = A (D x, 1)) ∧
      (∀ x ∈ S, ∀ u t : ℝ, G t (A (x, u)) = A (x, u + t)) ∧
      (∀ p, (Ψ p).2 = p.2) ∧
      (∀ p, p.2 ≤ 1 / 3 → Ψ p = p) ∧
      (∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2)) ∧
      ∀ x ∈ A.target, V' x = VectorField.mpullback 𝓘(ℝ, E)
        (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm (nativeSuspensionField Ψ) x := by
  obtain ⟨Ψ, hL, hΨheight, hleft, hright, hW, hF, hWheight, hWzero,
      hfix, -, hend, -, -, hfixed⟩ := exists_compact_native_level_suspension D hK I
  let L : Set (N × ℝ) := K ×ˢ Icc (1 / 3 : ℝ) (2 / 3)
  have hLA : L ⊆ A.source := by rw [hsource]; exact subset_univ L
  have hvertical (p : N × ℝ) (_ : p ∈ A.source) : nativeVerticalField (Z := Z) p ≠ 0 := by
    intro hz
    have hh := congrArg (fun v : Z × ℝ => v.2) hz
    exact one_ne_zero hh
  obtain ⟨V', hV', hnew, hzero, hgerm⟩ := exists_native_model_field_replacement A V hV
    nativeVerticalField (nativeSuspensionField Ψ) hW hmodel hvertical
    (fun p _ => hWzero p) hL hLA hfix
  let C := A '' L
  have hC : IsCompact C := hL.image_of_continuousOn
    (A.contMDiffOn_toFun.continuousOn.mono hLA)
  have hslab (p : N × ℝ) (hp : p ∈ L) : p.2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hCsub : C ⊆ A.target ∩ f ⁻¹' Ioo (b - s) b := by
    rintro x ⟨p, hp, rfl⟩
    refine ⟨A.map_source' (hLA hp), ?_⟩
    change f (A p) ∈ Ioo (b - s) b
    rw [hheight p (hslab p hp)]
    constructor <;> nlinarith [(hslab p hp).1, (hslab p hp).2]
  let R := PartialChart.restrictSource A
    (isOpen_univ.prod (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) 1)))
  have hRheight (p : N × ℝ) (hp : p ∈ R.source) : f (R p) = b - s * p.2 :=
    hheight p hp.2.2
  have hnegC (x : M) (hx : x ∈ C) : mvfderiv 𝓘(ℝ, E) f x (V' x) = -s := by
    rcases hx with ⟨p, hp, rfl⟩
    have hpR : p ∈ R.source := ⟨hLA hp, mem_univ _, hslab p hp⟩
    rw [hnew (A p) (A.map_source' (hLA hp))]
    change mvfderiv 𝓘(ℝ, E) f (R p)
      (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
        R.symm (nativeSuspensionField Ψ) (R p)) = -s
    rw [mvfderiv_native_level_height R hf hRheight _ (R.map_source' hpR), hWheight, mul_one]
  have hV'₁ := hV'.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  let G := FlowConstruction.compactFlow hV'₁
  have hG (x : M) : IsMIntegralCurve (fun t => G t x) V' :=
    FlowConstruction.isMIntegralCurve_compactFlow hV'₁ x
  have hstay (p : N × ℝ) (t : ℝ) : nativeSuspensionFlow Ψ t p ∈ A.source := by
    rw [hsource]
    exact mem_univ _
  have hfull (p : N × ℝ) (t : ℝ) : G t (A p) = A (nativeSuspensionFlow Ψ t p) :=
    native_model_flow_all_time A hV'₁ G hG (nativeSuspensionFlow Ψ)
      (nativeSuspensionField Ψ) hF hnew (hstay p) t
  have hinv := native_model_target_invariant A hV'₁ G hG (nativeSuspensionFlow Ψ)
    (nativeSuspensionField Ψ) hF hnew (fun p _ => hstay p)
  have hcomp := flow_complement_invariant G hinv
  refine ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, ?_, hgerm, hinv, ?_,
    hfull, ?_, ?_, hΨheight, hleft, hright, hnew⟩
  · intro x hx
    by_cases hc : x ∈ C
    · rw [hnegC x hc]
      exact neg_neg_of_pos hs
    · rw [(hgerm x hc).self_of_nhds]
      exact hx
  · intro x hx t
    have hagree (u : ℝ) : V' (G u x) = V (G u x) :=
      (hgerm (G u x) (fun h => hcomp x hx u (hCsub h).1)).self_of_nhds
    rcases le_total 0 t with ht | ht
    · exact FlowCancellation.native_flow_eq_on_positive_halfline
        (hV.of_le (by simp)) H G hH hG (fun u _ => hagree u) t ht
    · exact FlowCancellation.native_flow_eq_on_negative_halfline
        (hV.of_le (by simp)) H G hH hG (fun u _ => hagree u) t ht
  · intro x
    rw [hfull, hend]
  · intro x hx u t
    rw [hfull, hfixed x hx u t]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
