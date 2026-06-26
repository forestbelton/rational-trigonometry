/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Proportionality of lines

Two lines are `Proportional` when their coefficients agree up to a nonzero
scalar. This is an equivalence relation (`proportionalSetoid`) and respects
incidence (`propor_point`).
-/

variable {K : Type*} [Field K]

def Proportional (l m : Line K) : Prop :=
  ∃ k ≠ 0, l.a = k * m.a ∧ l.b = k * m.b ∧ l.c = k * m.c

theorem propor_refl (l : Line K) : Proportional l l
:= by
  unfold Proportional
  exact ⟨1, by simp⟩

theorem propor_symm {l m : Line K} : Proportional l m → Proportional m l
:= by
  intro ⟨k, kn0, pa, pb, pc⟩
  unfold Proportional at ⊢
  refine ⟨1/k, ?_, ?_⟩
  · intro invk0
    simp only [one_div, inv_eq_zero] at invk0
    exact kn0 invk0
  · rw [pa, pb, pc]
    field_simp
    simp

theorem propor_trans {l m n : Line K}
: Proportional l m
→ Proportional m n
→ Proportional l n
:= by
  intro ⟨k₀, k₀n0, k₀a, k₀b, k₀c⟩ ⟨k₁, k₁n0, k₁a, k₁b, k₁c⟩
  unfold Proportional at ⊢
  refine ⟨k₀ * k₁, ?_, ?_, ?_, ?_⟩
  · intro invk0
    rcases mul_eq_zero.mp invk0 with k₀0 | k₁0
    · exact k₀n0 k₀0
    · exact k₁n0 k₁0
  · rwa [mul_assoc, ← k₁a]
  · rwa [mul_assoc, ← k₁b]
  · rwa [mul_assoc, ← k₁c]

instance proportionalSetoid (K : Type*) [Field K] : Setoid (Line K) where
  r := Proportional
  iseqv := {
    refl := propor_refl,
    symm := propor_symm,
    trans := propor_trans,
  }

theorem propor_point (l m : Line K) : Proportional l m → (HasPoint l p ↔ HasPoint m p)
:= by
  unfold HasPoint Proportional
  intro ⟨k, kn0, hla, hlb, hlc⟩
  constructor
  · intro lp
    rw [hla, hlb, hlc] at lp
    apply mul_left_cancel₀ kn0
    linear_combination lp
  · intro mp
    rw [hla, hlb, hlc]
    linear_combination k * mp
