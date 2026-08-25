import StackExchange.Puzzling139335.SquareSymmetry.Eight

/-!
# Algebraic alternatives for two square symmetries

The exhaustive coordinate forms of square symmetries imply that each is a
quarter-turn or an involution. Two involutions either commute or have a
quarter-turn as their composite.
-/

open Set

namespace Puzzling139335.SymmetryOrbit

noncomputable section

/-- Squaring this isometry gives the half-turn about the square center. -/
def IsQuarterTurn (e : Plane ≃ᵃⁱ[ℝ] Plane) : Prop :=
  ∀ x, e (e x) = AffineIsometryEquiv.pointReflection ℝ squareCenter x

private theorem center_reflection_formula (p : Plane) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter p =
      (!₂[1 - p 0, 1 - p 1] : Plane) := by
  ext i
  fin_cases i <;>
    simp [AffineIsometryEquiv.pointReflection_apply, squareCenter,
      vsub_eq_sub, vadd_eq_add] <;> ring

private theorem involutive_of_direct_form (e : Plane ≃ᵃⁱ[ℝ] Plane) (b : Fin 4)
    (he : ∀ p, e p = SquareSymmetry.cornerFlip b p) : Function.Involutive e := by
  intro p
  rw [he, he]
  exact SquareSymmetry.cornerFlip_involutive b p

private theorem involutive_of_even_swap_form (e : Plane ≃ᵃⁱ[ℝ] Plane) (b : Fin 4)
    (hb : b = 0 ∨ b = 2)
    (he : ∀ p, e p = SquareSymmetry.cornerFlip b (!₂[p 1, p 0] : Plane)) :
    Function.Involutive e := by
  rcases hb with rfl | rfl <;> intro p <;> simp only [he] <;>
    ext i <;> fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private theorem quarter_of_odd_swap_form (e : Plane ≃ᵃⁱ[ℝ] Plane) (b : Fin 4)
    (hb : b = 1 ∨ b = 3)
    (he : ∀ p, e p = SquareSymmetry.cornerFlip b (!₂[p 1, p 0] : Plane)) :
    IsQuarterTurn e := by
  rcases hb with rfl | rfl <;> intro p <;>
    rw [center_reflection_formula] <;> simp only [he] <;>
    ext i <;> fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private theorem quarter_or_involution_forms (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (heS : e '' unitSquare ⊆ unitSquare) :
    IsQuarterTurn e ∨
      (∃ b : Fin 4, ∀ p, e p = SquareSymmetry.cornerFlip b p) ∨
      (∃ b : Fin 4, (b = 0 ∨ b = 2) ∧
        ∀ p, e p = SquareSymmetry.cornerFlip b (!₂[p 1, p 0] : Plane)) := by
  obtain ⟨b, he | he⟩ := SquareSymmetry.coordinate_forms_of_maps_square_into_square e heS
  · exact Or.inr (Or.inl ⟨b, he⟩)
  · fin_cases b
    · exact Or.inr (Or.inr ⟨0, Or.inl rfl, he⟩)
    · exact Or.inl (quarter_of_odd_swap_form e 1 (Or.inl rfl) he)
    · exact Or.inr (Or.inr ⟨2, Or.inr rfl, he⟩)
    · exact Or.inl (quarter_of_odd_swap_form e 3 (Or.inr rfl) he)

/-- Every affine isometry taking the square into itself is a quarter-turn or an
involution; the identity is allowed among the involutions. -/
theorem square_symmetry_classification (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (heS : e '' unitSquare ⊆ unitSquare) :
    IsQuarterTurn e ∨ Function.Involutive e := by
  rcases quarter_or_involution_forms e heS with hq | ⟨b, he⟩ | ⟨b, hb, he⟩
  · exact Or.inl hq
  · exact Or.inr (involutive_of_direct_form e b he)
  · exact Or.inr (involutive_of_even_swap_form e b hb he)

private theorem commute_of_direct_forms (e f : Plane ≃ᵃⁱ[ℝ] Plane) (b c : Fin 4)
    (he : ∀ p, e p = SquareSymmetry.cornerFlip b p)
    (hf : ∀ p, f p = SquareSymmetry.cornerFlip c p) : Function.Commute e f := by
  intro p
  simp only [he, hf]
  fin_cases b <;> fin_cases c <;> ext i <;> fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private theorem classify_direct_swap (e f : Plane ≃ᵃⁱ[ℝ] Plane) (b c : Fin 4)
    (hc : c = 0 ∨ c = 2)
    (he : ∀ p, e p = SquareSymmetry.cornerFlip b p)
    (hf : ∀ p, f p = SquareSymmetry.cornerFlip c (!₂[p 1, p 0] : Plane)) :
    IsQuarterTurn (e.trans f) ∨ Function.Commute e f := by
  rcases hc with rfl | rfl <;> fin_cases b
  all_goals
    first
    | right
      intro p
      simp only [he, hf]
      ext i
      fin_cases i <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]
      done
    | left
      intro p
      change f (e (f (e p))) = AffineIsometryEquiv.pointReflection ℝ squareCenter p
      rw [center_reflection_formula]
      simp only [he, hf]
      ext i
      fin_cases i <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private theorem classify_swap_direct (e f : Plane ≃ᵃⁱ[ℝ] Plane) (b c : Fin 4)
    (hb : b = 0 ∨ b = 2)
    (he : ∀ p, e p = SquareSymmetry.cornerFlip b (!₂[p 1, p 0] : Plane))
    (hf : ∀ p, f p = SquareSymmetry.cornerFlip c p) :
    IsQuarterTurn (e.trans f) ∨ Function.Commute e f := by
  rcases hb with rfl | rfl <;> fin_cases c
  all_goals
    first
    | right
      intro p
      simp only [he, hf]
      ext i
      fin_cases i <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]
      done
    | left
      intro p
      change f (e (f (e p))) = AffineIsometryEquiv.pointReflection ℝ squareCenter p
      rw [center_reflection_formula]
      simp only [he, hf]
      ext i
      fin_cases i <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private theorem commute_of_even_swap_forms (e f : Plane ≃ᵃⁱ[ℝ] Plane) (b c : Fin 4)
    (hb : b = 0 ∨ b = 2) (hc : c = 0 ∨ c = 2)
    (he : ∀ p, e p = SquareSymmetry.cornerFlip b (!₂[p 1, p 0] : Plane))
    (hf : ∀ p, f p = SquareSymmetry.cornerFlip c (!₂[p 1, p 0] : Plane)) :
    Function.Commute e f := by
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    intro p <;> simp only [he, hf] <;> ext i <;> fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

/-- Two square symmetries either include a quarter-turn, or are involutions
whose composite is a quarter-turn or which commute. No distinctness hypothesis
is needed. -/
theorem square_symmetry_pair_classification (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (heS : e '' unitSquare ⊆ unitSquare) (hfS : f '' unitSquare ⊆ unitSquare) :
    IsQuarterTurn e ∨ IsQuarterTurn f ∨
      (Function.Involutive e ∧ Function.Involutive f ∧
        (IsQuarterTurn (e.trans f) ∨ Function.Commute e f)) := by
  rcases quarter_or_involution_forms e heS with heq | ⟨b, he⟩ | ⟨b, hb, he⟩
  · exact Or.inl heq
  · rcases quarter_or_involution_forms f hfS with hfq | ⟨c, hf⟩ | ⟨c, hc, hf⟩
    · exact Or.inr (Or.inl hfq)
    · exact Or.inr (Or.inr ⟨involutive_of_direct_form e b he,
        involutive_of_direct_form f c hf, Or.inr (commute_of_direct_forms e f b c he hf)⟩)
    · exact Or.inr (Or.inr ⟨involutive_of_direct_form e b he,
        involutive_of_even_swap_form f c hc hf, classify_direct_swap e f b c hc he hf⟩)
  · rcases quarter_or_involution_forms f hfS with hfq | ⟨c, hf⟩ | ⟨c, hc, hf⟩
    · exact Or.inr (Or.inl hfq)
    · exact Or.inr (Or.inr ⟨involutive_of_even_swap_form e b hb he,
        involutive_of_direct_form f c hf, classify_swap_direct e f b c hb he hf⟩)
    · exact Or.inr (Or.inr ⟨involutive_of_even_swap_form e b hb he,
        involutive_of_even_swap_form f c hc hf,
        Or.inr (commute_of_even_swap_forms e f b c hb hc he hf)⟩)

end

end Puzzling139335.SymmetryOrbit
