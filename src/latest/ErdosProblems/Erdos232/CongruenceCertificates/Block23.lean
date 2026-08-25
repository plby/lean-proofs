/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.MaskCongruence

namespace Erdos232

theorem maskCongruent_23_000 :
    MaskCongruent 4489217 4719617 :=
  MaskMapValid.maskCongruent (code := 19972654011647084285254579019461) (by decide)

theorem maskCongruent_23_001 :
    MaskCongruent 4489224 4719680 :=
  MaskMapValid.maskCongruent (code := 19972654011647084285254579092463) (by decide)

theorem maskCongruent_23_002 :
    MaskCongruent 4489224 5505056 :=
  MaskMapValid.maskCongruent (code := 16341307198621125030105563183415) (by decide)

theorem maskCongruent_23_003 :
    MaskCongruent 4489225 4719681 :=
  MaskMapValid.maskCongruent (code := 19972654011647084285254579092463) (by decide)

theorem maskCongruent_23_004 :
    MaskCongruent 4489236 4719636 :=
  MaskMapValid.maskCongruent (code := 19972654011647084285254579581259) (by decide)

theorem maskCongruent_23_005 :
    MaskCongruent 4489240 4719684 :=
  MaskMapValid.maskCongruent (code := 19972654011647084285254579652145) (by decide)

theorem maskCongruent_23_006 :
    MaskCongruent 4491272 5507104 :=
  MaskMapValid.maskCongruent (code := 16341307198621135511012900236612) (by decide)

theorem maskCongruent_23_007 :
    MaskCongruent 4505600 4736000 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798121516787) (by decide)

theorem maskCongruent_23_008 :
    MaskCongruent 4505601 4736001 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798121516787) (by decide)

theorem maskCongruent_23_009 :
    MaskCongruent 4505604 4736016 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798121518903) (by decide)

theorem maskCongruent_23_010 :
    MaskCongruent 4505608 4736064 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798121589789) (by decide)

theorem maskCongruent_23_011 :
    MaskCongruent 4505609 4736065 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798121589789) (by decide)

theorem maskCongruent_23_012 :
    MaskCongruent 4505616 4736004 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798122076469) (by decide)

theorem maskCongruent_23_013 :
    MaskCongruent 4505620 4736020 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798122078585) (by decide)

theorem maskCongruent_23_014 :
    MaskCongruent 4505624 4736068 :=
  MaskMapValid.maskCongruent (code := 19972654011809383993798122149471) (by decide)

theorem maskCongruent_23_015 :
    MaskCongruent 4723776 5505060 :=
  MaskMapValid.maskCongruent (code := 16341608903322613851509211105057) (by decide)

theorem maskCongruent_23_016 :
    MaskCongruent 4751369 4751425 :=
  MaskMapValid.maskCongruent (code := 19973740802201899193430154716078) (by decide)

theorem maskCongruent_23_017 :
    MaskCongruent 4751384 4751428 :=
  MaskMapValid.maskCongruent (code := 19973740802201899193430155275760) (by decide)

theorem maskCongruent_23_018 :
    MaskCongruent 4767748 4767760 :=
  MaskMapValid.maskCongruent (code := 19973740802364198901973697142518) (by decide)

theorem maskCongruent_23_019 :
    MaskCongruent 4767752 4767808 :=
  MaskMapValid.maskCongruent (code := 19973740802364198901973697213404) (by decide)

theorem maskCongruent_23_020 :
    MaskCongruent 4767753 4767809 :=
  MaskMapValid.maskCongruent (code := 19973740802364198901973697213404) (by decide)

theorem maskCongruent_23_021 :
    MaskCongruent 4767768 4767812 :=
  MaskMapValid.maskCongruent (code := 19973740802364198901973697773086) (by decide)

theorem maskCongruent_23_022 :
    MaskCongruent 5505064 5537800 :=
  MaskMapValid.maskCongruent (code := 16346455664781952611812475186128) (by decide)

theorem maskCongruent_23_023 :
    MaskCongruent 5507112 5539848 :=
  MaskMapValid.maskCongruent (code := 16346455664781963092719812239325) (by decide)

private theorem maskCongruent_suffix_23_023 :
    ∀ c : (Nat × Nat × Int), c ∈ [(5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_singleton] at hc
  subst c
  exact maskCongruent_23_023

private theorem maskCongruent_suffix_23_022 :
    ∀ c : (Nat × Nat × Int), c ∈ [(5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_022
  · exact maskCongruent_suffix_23_023 c hc

private theorem maskCongruent_suffix_23_021 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_021
  · exact maskCongruent_suffix_23_022 c hc

private theorem maskCongruent_suffix_23_020 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_020
  · exact maskCongruent_suffix_23_021 c hc

private theorem maskCongruent_suffix_23_019 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_019
  · exact maskCongruent_suffix_23_020 c hc

private theorem maskCongruent_suffix_23_018 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_018
  · exact maskCongruent_suffix_23_019 c hc

private theorem maskCongruent_suffix_23_017 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_017
  · exact maskCongruent_suffix_23_018 c hc

private theorem maskCongruent_suffix_23_016 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_016
  · exact maskCongruent_suffix_23_017 c hc

private theorem maskCongruent_suffix_23_015 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_015
  · exact maskCongruent_suffix_23_016 c hc

private theorem maskCongruent_suffix_23_014 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_014
  · exact maskCongruent_suffix_23_015 c hc

private theorem maskCongruent_suffix_23_013 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_013
  · exact maskCongruent_suffix_23_014 c hc

private theorem maskCongruent_suffix_23_012 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_012
  · exact maskCongruent_suffix_23_013 c hc

private theorem maskCongruent_suffix_23_011 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_011
  · exact maskCongruent_suffix_23_012 c hc

private theorem maskCongruent_suffix_23_010 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_010
  · exact maskCongruent_suffix_23_011 c hc

private theorem maskCongruent_suffix_23_009 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_009
  · exact maskCongruent_suffix_23_010 c hc

private theorem maskCongruent_suffix_23_008 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_008
  · exact maskCongruent_suffix_23_009 c hc

private theorem maskCongruent_suffix_23_007 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_007
  · exact maskCongruent_suffix_23_008 c hc

private theorem maskCongruent_suffix_23_006 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4491272, 5507104, 113394222), (4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_006
  · exact maskCongruent_suffix_23_007 c hc

private theorem maskCongruent_suffix_23_005 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4489240, 4719684, -162785421), (4491272, 5507104, 113394222), (4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_005
  · exact maskCongruent_suffix_23_006 c hc

private theorem maskCongruent_suffix_23_004 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4489236, 4719636, -239857632), (4489240, 4719684, -162785421), (4491272, 5507104, 113394222), (4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_004
  · exact maskCongruent_suffix_23_005 c hc

private theorem maskCongruent_suffix_23_003 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4489225, 4719681, -120736053), (4489236, 4719636, -239857632), (4489240, 4719684, -162785421), (4491272, 5507104, 113394222), (4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_003
  · exact maskCongruent_suffix_23_004 c hc

private theorem maskCongruent_suffix_23_002 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4489224, 5505056, -69839133), (4489225, 4719681, -120736053), (4489236, 4719636, -239857632), (4489240, 4719684, -162785421), (4491272, 5507104, 113394222), (4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_002
  · exact maskCongruent_suffix_23_003 c hc

private theorem maskCongruent_suffix_23_001 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4489224, 4719680, 160471052), (4489224, 5505056, -69839133), (4489225, 4719681, -120736053), (4489236, 4719636, -239857632), (4489240, 4719684, -162785421), (4491272, 5507104, 113394222), (4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_001
  · exact maskCongruent_suffix_23_002 c hc

private theorem maskCongruent_suffix_23_000 :
    ∀ c : (Nat × Nat × Int), c ∈ [(4489217, 4719617, 136002196), (4489224, 4719680, 160471052), (4489224, 5505056, -69839133), (4489225, 4719681, -120736053), (4489236, 4719636, -239857632), (4489240, 4719684, -162785421), (4491272, 5507104, 113394222), (4505600, 4736000, 86389790), (4505601, 4736001, -83590859), (4505604, 4736016, -119876439), (4505608, 4736064, -15827094), (4505609, 4736065, -56537170), (4505616, 4736004, -387746007), (4505620, 4736020, 638064904), (4505624, 4736068, 374809555), (4723776, 5505060, 55712557), (4751369, 4751425, -94952655), (4751384, 4751428, -35363714), (4767748, 4767760, 68926203), (4767752, 4767808, -43222421), (4767753, 4767809, 7062562), (4767768, 4767812, 138658897), (5505064, 5537800, -102603613), (5507112, 5539848, 169269087)] → MaskCongruent c.1 c.2.1 := by
  intro c hc
  rw [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst c; exact maskCongruent_23_000
  · exact maskCongruent_suffix_23_001 c hc

theorem maskCongruent_block23 :
    ∀ c ∈ atomCongruenceWeights23, MaskCongruent c.1 c.2.1 := by
  simpa only [atomCongruenceWeights23] using maskCongruent_suffix_23_000

end Erdos232
