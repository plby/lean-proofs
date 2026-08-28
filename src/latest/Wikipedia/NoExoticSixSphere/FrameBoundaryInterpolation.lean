import Wikipedia.NoExoticSixSphere.CompactParameter
import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Replacing frame data near a compact protected set

Two ambient operator families agree on the protected set. Compactness in
the interpolation parameter supplies a neighborhood on which all projected
interpolates remain injective. A continuous cutoff then installs the new
family near that set without losing injectivity anywhere in the compact region.
-/

noncomputable section

open Set Function
open scoped unitInterval Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

variable {E : Type*} [NormedAddCommGroup E]
variable {N n : ℕ}

theorem exists_boundaryInterpolation {K S : Set E} (hK : IsCompact K) (hS : IsCompact S)
    (A F : C(E, Vector n →L[ℝ] Vector N))
    (P : E → Vector N →L[ℝ] Vector N) (hP : ContinuousOn P K)
    (hA : ∀ x ∈ K, Injective ((P x).comp (A x))) (heq : EqOn F A S) :
    ∃ B : C(E, Vector n →L[ℝ] Vector N),
      (∀ x ∈ K, Injective ((P x).comp (B x))) ∧
      ∃ U : Set E, IsOpen U ∧ S ⊆ U ∧ EqOn B F U := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let V : Set K := {x | ∀ t : unitInterval,
    Injective ((P x).comp (A x + (t : ℝ) • (F x - A x)))}
  have hpC : Continuous (fun x : K ↦ P x) := continuousOn_iff_continuous_domRestrict.mp hP
  have hV : IsOpen V := by
    have haC : Continuous (fun z : K × unitInterval ↦ A z.1) :=
      (A.continuous.comp continuous_subtype_val).comp continuous_fst
    have hfC : Continuous (fun z : K × unitInterval ↦ F z.1) :=
      (F.continuous.comp continuous_subtype_val).comp continuous_fst
    have hc : Continuous (fun z : K × unitInterval ↦
        (P z.1).comp (A z.1 + (z.2 : ℝ) • (F z.1 - A z.1))) :=
      (hpC.comp continuous_fst).clm_comp
        (haC.add ((continuous_subtype_val.comp continuous_snd).smul (hfC.sub haC)))
    exact isOpen_forall_compact (ContinuousLinearMap.isOpen_injective.preimage hc)
  let W : Set E := (Subtype.val '' Vᶜ)ᶜ
  have hW : IsOpen W :=
    (hV.isClosed_compl.isCompact.image continuous_subtype_val).isClosed.isOpen_compl
  have hSW : S ⊆ W := by
    intro x hx
    rintro ⟨y, hy, rfl⟩
    apply hy
    intro t
    rw [heq hx, sub_self, smul_zero, add_zero]
    exact hA y y.property
  have hgood (x : E) (hx : x ∈ K) (hw : x ∈ W) (t : unitInterval) :
      Injective ((P x).comp (A x + (t : ℝ) • (F x - A x))) := by
    have hv : (⟨x, hx⟩ : K) ∈ V := by
      by_contra h
      exact hw ⟨⟨x, hx⟩, h, rfl⟩
    exact hv t
  obtain ⟨U, hU, hSU, hUW⟩ := hS.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hSW)
  have hdis : Disjoint Wᶜ (closure U) := disjoint_left.mpr (fun x hx hu ↦ hx (hUW hu))
  obtain ⟨χ, hχ0, hχ1, hχI⟩ :=
    exists_continuous_zero_one_of_isClosed hW.isClosed_compl isClosed_closure hdis
  let B : C(E, Vector n →L[ℝ] Vector N) :=
    ⟨fun x ↦ A x + χ x • (F x - A x),
      A.continuous.add (χ.continuous.smul (F.continuous.sub A.continuous))⟩
  refine ⟨B, ?_, U, hU, hSU, ?_⟩
  · intro x hx
    by_cases hw : x ∈ W
    · exact hgood x hx hw ⟨χ x, hχI x⟩
    · change Injective ((P x).comp (A x + χ x • (F x - A x)))
      rw [hχ0 hw]
      simpa only [Pi.zero_apply, zero_smul, add_zero] using hA x hx
  · intro x hx
    change A x + χ x • (F x - A x) = F x
    rw [hχ1 (subset_closure hx)]
    simp only [Pi.one_apply, one_smul]
    abel

end NoExoticSixSphere.Stiefel
