import Wikipedia.SmoothSixDPoincare.SmoothHomotopyCollars
import Wikipedia.SmoothSixDPoincare.GlobalImageAvoidance

/-!
# Homotopies in the actual complement of a high-codimension smooth image

Relative general position removes the obstacle from a cylinder homotopy while
fixing whole endpoint collars. Both the homotopy and its smooth representative
then live in the genuine open complement. The dimension bound includes the
time direction and does not apply to a codimension-two obstacle for circle maps.
-/

noncomputable section

open Set ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ImageComplement

variable {Y N : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [TopologicalSpace N] [T2Space N]

def domain (g : C(Y, N)) : Opens N :=
  ⟨(range g)ᶜ, (isCompact_range g.continuous).isClosed.isOpen_compl⟩

def inclusion (g : C(Y, N)) : C(domain g, N) := ⟨Subtype.val, continuous_subtype_val⟩

variable {E E' G H H' K X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [CompactSpace X]
  [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [ChartedSpace K N] [IsManifold J ∞ N]

/-- The actual complement admits a smooth homotopy with full fixed endpoint collars. -/
theorem exists_smooth_homotopy_of_ambient_homotopic (g : C(Y, N))
    (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g))
    (hf₀ : ContMDiff I J ∞ f₀) (hf₁ : ContMDiff I J ∞ f₁)
    (hambient : ((inclusion g).comp f₀).Homotopic ((inclusion g).comp f₁)) :
    ∃ H : f₀.Homotopy f₁, ContMDiff ((𝓡∂ 1).prod I) J ∞ H ∧
      (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f₀ x) ∧
      (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = f₁ x) := by
  obtain ⟨H⟩ := hambient
  have hval : ContMDiff J J ∞ (inclusion g) := contMDiff_subtype_val
  have hf₀val : ContMDiff I J ∞ ((inclusion g).comp f₀) := hval.comp hf₀
  have hf₁val : ContMDiff I J ∞ ((inclusion g).comp f₁) := hval.comp hf₁
  obtain ⟨H, hH, hlo, hhi⟩ := ManifoldSmoothing.exists_smooth_homotopy_with_collars
    hf₀val hf₁val H
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × E) +
      Module.finrank ℝ E' < Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ q ∈ ManifoldSmoothing.homotopyCollars X, H q ∉ range g := by
    rintro ⟨t, x⟩ (ht | ht)
    · rw [hlo t x ht]
      exact (f₀ x).property
    · rw [hhi t x ht]
      exact (f₁ x).property
  obtain ⟨F, hF, hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel H.toContinuousMap g hH hg hd
      ManifoldSmoothing.isClosed_homotopyCollars hfixed
  have heq : EqOn F H (ManifoldSmoothing.homotopyCollars X) :=
    fun _ hq => (hrel.fst_eq_snd hq).symm
  have havoid : ∀ q, F q ∈ domain g := by
    intro q
    change F q ∉ range g
    exact fun hq => Set.disjoint_left.mp hdisjoint ⟨q, rfl⟩ hq
  let A : C(unitInterval × X, domain g) :=
    ⟨fun q => ⟨F q, havoid q⟩, F.continuous.subtype_mk _⟩
  have hA : ContMDiff ((𝓡∂ 1).prod I) J ∞ A :=
    (ContMDiff.subtypeVal_comp_iff (domain g) A).mp hF
  have hAlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : A (t, x) = f₀ x := by
    apply Subtype.ext
    exact (heq (show (t, x) ∈ ManifoldSmoothing.homotopyCollars X from Or.inl ht)).trans
      (hlo t x ht)
  have hAhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : A (t, x) = f₁ x := by
    apply Subtype.ext
    exact (heq (show (t, x) ∈ ManifoldSmoothing.homotopyCollars X from Or.inr ht)).trans
      (hhi t x ht)
  exact ⟨{
    toContinuousMap := A
    map_zero_left := fun x => hAlo 0 x (by norm_num)
    map_one_left := fun x => hAhi 1 x (by norm_num) }, hA, hAlo, hAhi⟩

include I in
/-- Arbitrary continuous maps homotopic in the ambient manifold are homotopic in its
actual image complement under the cylinder dimension bound. -/
theorem homotopic_of_ambient_homotopic (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g))
    (hambient : ((inclusion g).comp f₀).Homotopic ((inclusion g).comp f₁)) :
    f₀.Homotopic f₁ := by
  obtain ⟨f₀', hf₀', h₀⟩ := ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₀
  obtain ⟨f₁', hf₁', h₁⟩ := ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₁
  have ha₀ := (Homotopic.refl (inclusion g)).comp h₀
  have ha₁ := (Homotopic.refl (inclusion g)).comp h₁
  obtain ⟨H, -⟩ := exists_smooth_homotopy_of_ambient_homotopic g hg hdim f₀' f₁' hf₀' hf₁'
    (ha₀.symm.trans (hambient.trans ha₁))
  exact h₀.trans ((show f₀'.Homotopic f₁' from ⟨H⟩).trans h₁.symm)

end Wikipedia.SmoothSixDPoincare.ImageComplement
