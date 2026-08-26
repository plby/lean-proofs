import ErdosProblems.Erdos1148.QuadraticOrderConductor
import Mathlib.RingTheory.Conductor

/-! # Ideal extension and contraction away from a conductor -/

namespace Erdos1148.DukeArithmetic

section Rings

variable {A B : Type*} [CommRing A] [CommRing B]

theorem map_comap_eq_of_conductor_coprime (f : A →+* B) (C : Ideal B)
    (hC : ∀ c ∈ C, c ∈ f.range) (J : Ideal B) (hJ : J ⊔ C = ⊤) :
    (J.comap f).map f = J := by
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hJ)
  obtain ⟨c₀, hc₀⟩ := hC c hc
  have ha₀ : f (1 - c₀) = a := by
    rw [map_sub, map_one, hc₀]
    linear_combination -hac
  have ha_mem : 1 - c₀ ∈ J.comap f := by
    change f (1 - c₀) ∈ J
    rw [ha₀]
    exact ha
  have ham : a ∈ (J.comap f).map f := ha₀ ▸ Ideal.mem_map_of_mem f ha_mem
  have hcx : c * x ∈ C := C.mul_mem_right x hc
  obtain ⟨b₀, hb₀⟩ := hC (c * x) hcx
  have hb_mem : b₀ ∈ J.comap f := by
    change f b₀ ∈ J
    rw [hb₀]
    exact J.mul_mem_left c hx
  have hbm : c * x ∈ (J.comap f).map f := hb₀ ▸ Ideal.mem_map_of_mem f hb_mem
  have hsum := ((J.comap f).map f).add_mem
    (((J.comap f).map f).mul_mem_left x ham) hbm
  have heq : x * a + c * x = x := by
    calc
      x * a + c * x = x * (a + c) := by ring
      _ = x := by rw [hac, mul_one]
  rwa [heq] at hsum

theorem comap_coprime_of_conductor_coprime (f : A →+* B)
    (C : Ideal B) (hC : ∀ c ∈ C, c ∈ f.range) (J : Ideal B) (hJ : J ⊔ C = ⊤) :
    J.comap f ⊔ C.comap f = ⊤ := by
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hJ)
  obtain ⟨c₀, hc₀⟩ := hC c hc
  have ha₀ : f (1 - c₀) = a := by
    rw [map_sub, map_one, hc₀]
    linear_combination -hac
  apply (Ideal.eq_top_iff_one _).mpr
  apply Submodule.mem_sup.mpr
  refine ⟨1 - c₀, ?_, c₀, ?_, by ring⟩
  · change f (1 - c₀) ∈ J
    rw [ha₀]
    exact ha
  · change f c₀ ∈ C
    rw [hc₀]
    exact hc

theorem conductor_mul_mem_map_image (f : A →+* B) (C : Ideal B)
    (hC : ∀ c ∈ C, c ∈ f.range) (I : Ideal A) {z : B} (hz : z ∈ I.map f) :
    ∀ c : A, f c ∈ C → ∃ a ∈ I, f a = f c * z := by
  change z ∈ Submodule.span B (f '' (I : Set A)) at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      intro c _
      exact ⟨c * a, I.mul_mem_left c ha, map_mul f c a⟩
  | zero =>
      intro c _
      exact ⟨0, I.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
      intro c hc
      obtain ⟨a, ha, hax⟩ := hx c hc
      obtain ⟨b, hb, hby⟩ := hy c hc
      exact ⟨a + b, I.add_mem ha hb, by rw [map_add, hax, hby, mul_add]⟩
  | smul b z _ hz =>
      intro c hc
      obtain ⟨c', hc'⟩ := hC (f c * b) (C.mul_mem_right b hc)
      have hc'C : f c' ∈ C := by rw [hc']; exact C.mul_mem_right b hc
      obtain ⟨a, ha, haz⟩ := hz c' hc'C
      refine ⟨a, ha, ?_⟩
      rw [haz, hc']
      change (f c * b) * z = f c * (b * z)
      ring

theorem comap_map_eq_of_conductor_coprime (f : A →+* B) (hf : Function.Injective f)
    (C : Ideal B) (hC : ∀ c ∈ C, c ∈ f.range) (I : Ideal A)
    (hI : I ⊔ C.comap f = ⊤) : (I.map f).comap f = I := by
  apply le_antisymm _ Ideal.le_comap_map
  intro x hx
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hI)
  obtain ⟨b, hb, hbx⟩ := conductor_mul_mem_map_image f C hC I hx c hc
  have hbx' : b = c * x := hf (by rw [map_mul]; exact hbx)
  have hcx : c * x ∈ I := hbx' ▸ hb
  have hax : a * x ∈ I := I.mul_mem_right x ha
  have heq : a * x + c * x = x := by rw [← add_mul, hac, one_mul]
  simpa only [heq] using I.add_mem hax hcx

theorem comap_mul_of_conductor_coprime (f : A →+* B) (hf : Function.Injective f)
    (C : Ideal B) (hC : ∀ c ∈ C, c ∈ f.range) (J K : Ideal B)
    (hJ : J ⊔ C = ⊤) (hK : K ⊔ C = ⊤) :
    (J * K).comap f = J.comap f * K.comap f := by
  have hI := comap_coprime_of_conductor_coprime f C hC J hJ
  have hL := comap_coprime_of_conductor_coprime f C hC K hK
  have hprod : J.comap f * K.comap f ⊔ C.comap f = ⊤ :=
    (Ideal.mul_sup_eq_of_coprime_left hI).trans hL
  have h := comap_map_eq_of_conductor_coprime f hf C hC (J.comap f * K.comap f) hprod
  rw [Ideal.map_mul, map_comap_eq_of_conductor_coprime f C hC J hJ,
    map_comap_eq_of_conductor_coprime f C hC K hK] at h
  exact h

end Rings

end Erdos1148.DukeArithmetic
