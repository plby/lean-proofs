import ErdosProblems.Erdos1148.ConductorIdealCorrespondence
import ErdosProblems.Erdos1148.OrderClassExtension

/-! # Contractions of ideals prime to the conductor are invertible -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

section Rings

variable {A B : Type*} [CommRing A] [CommRing B]

lemma exists_ne_zero_congr_one_of_coprime (J C : Ideal B) (hJ₀ : J ≠ ⊥) (hJ : J ⊔ C = ⊤) :
    ∃ a ∈ J, a ≠ 0 ∧ a - 1 ∈ C := by
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hJ)
  by_cases ha₀ : a = 0
  · have hc₁ : c = 1 := by simpa [ha₀] using hac
    have hC : C = ⊤ := (Ideal.eq_top_iff_one _).mpr (hc₁ ▸ hc)
    obtain ⟨b, hb, hb₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ₀
    exact ⟨b, hb, hb₀, by rw [hC]; trivial⟩
  · refine ⟨a, ha, ha₀, ?_⟩
    have heq : a - 1 = -c := by linear_combination hac
    rw [heq]
    exact C.neg_mem hc

lemma span_singleton_coprime_of_sub_one_mem (C : Ideal A) {a : A} (ha : a - 1 ∈ C) :
    Ideal.span {a} ⊔ C = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  exact Submodule.mem_sup.mpr
    ⟨a, Ideal.subset_span (Set.mem_singleton a), -(a - 1), C.neg_mem ha, by ring⟩

theorem comap_span_singleton_of_conductor_congr_one (f : A →+* B) (hf : Function.Injective f)
    (C : Ideal B) (hC : ∀ c ∈ C, c ∈ f.range) (a : A) (ha : f a - 1 ∈ C) :
    (Ideal.span {f a}).comap f = Ideal.span {a} := by
  have ha' : a - 1 ∈ C.comap f := by
    change f (a - 1) ∈ C
    simpa only [map_sub, map_one] using ha
  have h := comap_map_eq_of_conductor_coprime f hf C hC (Ideal.span {a})
    (span_singleton_coprime_of_sub_one_mem _ ha')
  rw [Ideal.map_span, Set.image_singleton] at h
  exact h

end Rings

theorem isUnit_comap_of_conductor_coprime {A B K : Type*}
    [CommRing A] [IsDomain A] [CommRing B] [IsDedekindDomain B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A →+* B) (hf : Function.Injective f) (C : Ideal B)
    (hC : ∀ c ∈ C, c ∈ f.range) (J : Ideal B) (hJ₀ : J ≠ ⊥) (hJ : J ⊔ C = ⊤) :
    IsUnit (J.comap f : FractionalIdeal A⁰ K) := by
  obtain ⟨a, ha, ha₀, haC⟩ := exists_ne_zero_congr_one_of_coprime J C hJ₀ hJ
  obtain ⟨c, hc⟩ := hC (a - 1) haC
  let a₀ : A := c + 1
  have hfa : f a₀ = a := by
    change f (c + 1) = a
    rw [map_add, map_one, hc]
    ring
  have ha₀' : a₀ ≠ 0 := by
    intro hz
    apply ha₀
    rw [← hfa, hz, map_zero]
  have hdvd : J ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr ha)
  obtain ⟨L, hL⟩ := hdvd
  have haL : a ∈ L := by
    apply (Ideal.mul_le_right : J * L ≤ L)
    rw [← hL]
    exact Ideal.subset_span (Set.mem_singleton a)
  have hLC : L ⊔ C = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    exact Submodule.mem_sup.mpr ⟨a, haL, -(a - 1), C.neg_mem haC, by ring⟩
  have hprod : J.comap f * L.comap f = Ideal.span {a₀} := by
    rw [← comap_mul_of_conductor_coprime f hf C hC J L hJ hLC, ← hL, ← hfa]
    exact comap_span_singleton_of_conductor_congr_one f hf C hC a₀ (by simpa [hfa] using haC)
  have hprod' : (J.comap f : FractionalIdeal A⁰ K) * (L.comap f : FractionalIdeal A⁰ K) =
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K a₀) := by
    rw [← FractionalIdeal.coeIdeal_mul, hprod, FractionalIdeal.coeIdeal_span_singleton]
  have hane : algebraMap A K a₀ ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne ha₀'
  let v : Kˣ := Units.mk0 (algebraMap A K a₀) hane
  have hp : IsUnit (FractionalIdeal.spanSingleton A⁰ (algebraMap A K a₀)) :=
    ⟨toPrincipalIdeal A K v, coe_toPrincipalIdeal v⟩
  apply isUnit_of_mul_isUnit_left (y := (L.comap f : FractionalIdeal A⁰ K))
  rw [hprod']
  exact hp

end Erdos1148.DukeArithmetic
