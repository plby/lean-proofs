import Wikipedia.NoExoticSixSphere.SpherePoleCompactification
import Wikipedia.NoExoticSixSphere.EndingPathMayerVietoris

/-!
# The actual two-puncture cover for sphere path-space homology

Stereographic coordinates strongly contract a punctured sphere to any
specified point of its complement. Two distinct punctures give a genuine
open cover. The proved path-space Mayer--Vietoris construction then gives
the positive-degree integral homology splitting for its inverse images.
-/

noncomputable section

open Set Topology ContinuousMap
open scoped unitInterval
open Wikipedia.HopfProblem.SingularMayerVietoris

namespace NoExoticSixSphere.SpherePathCover

variable {n : ℕ}

def punctureHomeomorph (p : Sphere n) : ({p}ᶜ : Set (Sphere n)) ≃ₜ
    EuclideanSpace ℝ (Fin n) :=
  ((Homeomorph.setCongr (SpherePoleCompactification.chart_source p).symm).trans
    (SpherePoleCompactification.chart p).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (SpherePoleCompactification.chart_target p)).trans
      (Homeomorph.Set.univ _))

def contraction (p : Sphere n) (c : ({p}ᶜ : Set (Sphere n))) :
    (ContinuousMap.id ({p}ᶜ : Set (Sphere n))).HomotopyRel
      (ContinuousMap.const _ c) {c} where
  toFun u := (punctureHomeomorph p).symm
    ((1 - (u.1 : ℝ)) • punctureHomeomorph p u.2 + (u.1 : ℝ) • punctureHomeomorph p c)
  continuous_toFun := by
    have ht : Continuous (fun u : I × ({p}ᶜ : Set (Sphere n)) ↦ (u.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact (punctureHomeomorph p).symm.continuous.comp
      (((continuous_const.sub ht).smul ((punctureHomeomorph p).continuous.comp continuous_snd)).add
        (ht.smul continuous_const))
  map_zero_left z := by simp
  map_one_left z := by simp
  prop' s z hz := by
    have he : z = c := hz
    subst z
    change (punctureHomeomorph p).symm
      ((1 - (s : ℝ)) • punctureHomeomorph p c + (s : ℝ) • punctureHomeomorph p c) = c
    rw [← add_smul, sub_add_cancel, one_smul, Homeomorph.symm_apply_apply]

theorem punctures_cover (p q : Sphere n) (hpq : p ≠ q) :
    ({p}ᶜ : Set (Sphere n)) ∪ {q}ᶜ = univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hz : z = p
  · subst z
    exact Or.inr hpq
  · exact Or.inl hz

def homologyEquiv (p q b : Sphere n) (hpq : p ≠ q) (hbp : b ≠ p) (hbq : b ≠ q)
    (k : ℕ) (hk : k ≠ 0) :
    SingularHomology (EndingPath.restriction b {p}ᶜ ∩ EndingPath.restriction b {q}ᶜ :
      Set (EndingPath.Space b)) k ≃ₗ[ℤ]
      (SingularHomology (Path b b) k × SingularHomology (Path b b) k) :=
  EndingPath.loopCoverHomologyEquiv b {p}ᶜ {q}ᶜ isClosed_singleton.isOpen_compl
    isClosed_singleton.isOpen_compl (punctures_cover p q hpq) hbp hbq
    (contraction p ⟨b, hbp⟩) (contraction q ⟨b, hbq⟩) k hk

end NoExoticSixSphere.SpherePathCover
