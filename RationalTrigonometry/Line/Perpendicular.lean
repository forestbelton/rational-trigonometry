/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Proportional
import RationalTrigonometry.Line.Parallel

/-!
# Perpendicularity of lines

Two lines are `Perpendicular` when `a₁ * a₂ + b₁ * b₂ = 0`, together with the
construction `perp` of the perpendicular to a line through a given point.
-/

variable {K : Type*} [Field K]

def Perpendicular (l m : Line K) : Prop :=
  l.a * m.a + l.b * m.b = 0

theorem perp_symm (l m : Line K)
: Perpendicular l m
→ Perpendicular m l
:= by
  unfold Perpendicular
  intro lm
  linear_combination lm

theorem perp_not_para (l m : Line K)
: ¬Null l
→ Perpendicular l m
→ ¬Parallel l m
:= by
  unfold Perpendicular Parallel Null
  intro nnl lpm lmm
  have hma : (l.a * l.a + l.b * l.b) * m.a = 0 := by
    linear_combination l.a * lpm - l.b * lmm
  have hmb : (l.a * l.a + l.b * l.b) * m.b = 0 := by
    linear_combination l.b * lpm + l.a * lmm
  rcases mul_eq_zero.mp hma with lab0 | ma0
  · exact nnl lab0
  · rcases mul_eq_zero.mp hmb with lab0 | mb0
    · exact nnl lab0
    · rcases m.ab_ne_zero with man0 | mbn0
      · exact man0 ma0
      · exact mbn0 mb0

theorem perp_perp_para (l m n : Line K)
: Perpendicular l m
→ Perpendicular l n
→ Parallel m n
:= by
  unfold Perpendicular Parallel
  intro lm ln
  rcases l.ab_ne_zero with an0 | bn0
  · have h₀ : m.a = (-l.b * m.b) / l.a := by
      field_simp
      linear_combination lm
    have h₁ : n.a = (-l.b * n.b) / l.a := by
      field_simp
      linear_combination ln
    rw [h₀, h₁]
    ring
  · have h₀ : m.b = (-l.a * m.a) / l.b := by
      field_simp
      linear_combination lm
    have h₁ : n.b = (-l.a * n.a) / l.b := by
      field_simp
      linear_combination ln
    rw [h₀, h₁]
    ring

theorem perp_of_perp_para (l m n : Line K)
: Perpendicular l m
→ Perpendicular m n
→ Parallel l n
:= by
  unfold Perpendicular Parallel
  intro lm mn
  rcases m.ab_ne_zero with an0 | bn0
  · have h₀ : l.a = (-l.b * m.b) / m.a := by
      field_simp
      linear_combination lm
    have h₁ : n.a = (-m.b * n.b) / m.a := by
      field_simp
      linear_combination mn
    rw [h₀, h₁]
    ring
  · have h₀ : l.b = (-l.a * m.a) / m.b := by
      field_simp
      linear_combination lm
    have h₁ : n.b = (-m.a * n.a) / m.b := by
      field_simp
      linear_combination mn
    rw [h₀, h₁]
    ring

def perp (l : Line K) (p : Point K) : Line K := {
  a := -l.b,
  b := l.a,
  c := l.b * p.x - l.a * p.y,
  ab_ne_zero := by
    rcases l.ab_ne_zero with an0 | bn0
    · exact Or.inr an0
    · exact Or.inl (neg_ne_zero.mpr bn0)
}

theorem perp_perp (l : Line K) (p : Point K) : Perpendicular l (perp l p)
:= by
  unfold Perpendicular perp
  simp
  ring

theorem perp_point (l : Line K) (p : Point K) : HasPoint (perp l p) p
:= by
  unfold HasPoint perp
  simp

theorem perp_unique {l m : Line K}
: Perpendicular l m
→ HasPoint m p
→ Proportional (perp l p) m
:= by
  intro lm mp
  have h := perp_perp_para l (perp l p) m (perp_perp l p) lm
  have ⟨k, hk, ha, hb⟩ := (para_multiple (perp l p) m).mp h
  refine ⟨k, hk, ha, hb, ?_⟩
  unfold HasPoint at mp
  simp only [perp] at ha hb ⊢
  linear_combination -p.x * ha - p.y * hb - k * mp
