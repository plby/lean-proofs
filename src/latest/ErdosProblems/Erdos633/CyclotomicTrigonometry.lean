import ErdosProblems.Erdos633.CyclotomicEmbeddings

/-!
# Trigonometric values in the real cyclotomic coefficient field

Cosines are half the sum of a root power and its inverse. The constructed
real embeddings therefore have the required explicit action on every
integer-multiple cosine. Sines belong to the same field when a quarter
turn is an integer multiple of the generating angle.
-/

namespace Erdos633

theorem complex_cos_int_mul_root_expression (θ : ℝ) (m : ℤ) :
    (Real.cos ((m : ℝ) * θ) : ℂ) =
      (Complex.exp ((θ : ℂ) * Complex.I) ^ m +
        Complex.exp ((θ : ℂ) * Complex.I) ^ (-m)) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
  rw [Complex.ofReal_cos, mul_comm _ 2, Complex.two_cos]
  congr 1
  · rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  · rw [← Complex.exp_int_mul]
    congr 1
    push_cast
    ring

theorem cos_int_mul_mem_realRootField (θ : ℝ) (m : ℤ) :
    Real.cos ((m : ℝ) * θ) ∈ realRootField (Complex.exp ((θ : ℂ) * Complex.I)) := by
  let ζ := Complex.exp ((θ : ℂ) * Complex.I)
  let K := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  have hζ : ζ ∈ K := IntermediateField.mem_adjoin_simple_self ℚ ζ
  change (Real.cos ((m : ℝ) * θ) : ℂ) ∈ K
  rw [complex_cos_int_mul_root_expression]
  exact K.div_mem
    (K.add_mem (K.toSubfield.zpow_mem hζ m) (K.toSubfield.zpow_mem hζ (-m)))
    (natCast_mem K 2)

noncomputable def rootCosine (ζ : ℂ) (m : ℤ) :
    IntermediateField.adjoin ℚ ({ζ} : Set ℂ) :=
  let z : IntermediateField.adjoin ℚ ({ζ} : Set ℂ) :=
    ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  (z ^ m + z ^ (-m)) / 2

theorem realRootInclusion_cos_int_mul (θ : ℝ) (m : ℤ) :
    realRootInclusion (Complex.exp ((θ : ℂ) * Complex.I))
      ⟨Real.cos ((m : ℝ) * θ), cos_int_mul_mem_realRootField θ m⟩ =
      rootCosine (Complex.exp ((θ : ℂ) * Complex.I)) m := by
  apply Subtype.ext
  exact complex_cos_int_mul_root_expression θ m

theorem real_root_embedding_cos_int_mul (θ η : ℝ)
    (f : IntermediateField.adjoin ℚ ({Complex.exp ((θ : ℂ) * Complex.I)} : Set ℂ) →ₐ[ℚ] ℂ)
    (σ : realRootField (Complex.exp ((θ : ℂ) * Complex.I)) →+* ℝ)
    (hcompat : ∀ x, (σ x : ℂ) =
      f (realRootInclusion (Complex.exp ((θ : ℂ) * Complex.I)) x))
    (hf : f ⟨Complex.exp ((θ : ℂ) * Complex.I),
      IntermediateField.mem_adjoin_simple_self ℚ _⟩ = Complex.exp ((η : ℂ) * Complex.I))
    (m : ℤ) :
    σ ⟨Real.cos ((m : ℝ) * θ), cos_int_mul_mem_realRootField θ m⟩ =
      Real.cos ((m : ℝ) * η) := by
  apply Complex.ofReal_injective
  rw [hcompat, realRootInclusion_cos_int_mul]
  simp only [rootCosine, map_div₀, map_add, map_zpow₀, map_ofNat, hf]
  exact (complex_cos_int_mul_root_expression η m).symm

theorem sin_int_mul_mem_realRootField (θ : ℝ) (q m : ℤ)
    (hq : (q : ℝ) * θ = Real.pi / 2) :
    Real.sin ((m : ℝ) * θ) ∈ realRootField (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have h := cos_int_mul_mem_realRootField θ (q - m)
  have he : ((q - m : ℤ) : ℝ) * θ = Real.pi / 2 - (m : ℝ) * θ := by
    push_cast
    linear_combination hq
  rwa [he, Real.cos_pi_div_two_sub] at h

theorem exists_real_rotation_embedding (θ : ℝ) (n k : ℕ)
    (hn : 0 < n) (hθ : θ = 2 * Real.pi / n) (hk : k.Coprime n) :
    ∃ σ : realRootField (Complex.exp ((θ : ℂ) * Complex.I)) →+* ℝ,
      ∀ m : ℤ, σ ⟨Real.cos ((m : ℝ) * θ), cos_int_mul_mem_realRootField θ m⟩ =
        Real.cos ((k : ℝ) * ((m : ℝ) * θ)) := by
  let ζ := Complex.exp ((θ : ℂ) * Complex.I)
  have hζ : IsPrimitiveRoot ζ n := by
    have he : (θ : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I / n := by
      rw [hθ]
      push_cast
      ring
    simpa only [ζ, he] using Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨f, hf, σ, hcompat⟩ := exists_primitive_root_real_embedding ζ n k hn hζ hk
  have hfexp : f ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩ =
      Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [hf]
    change Complex.exp ((θ : ℂ) * Complex.I) ^ k = _
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨σ, fun m => ?_⟩
  have h := real_root_embedding_cos_int_mul θ ((k : ℝ) * θ) f σ hcompat hfexp m
  simpa only [mul_left_comm (m : ℝ) (k : ℝ) θ] using h

end Erdos633
