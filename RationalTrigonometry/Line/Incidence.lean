/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Proportional
import RationalTrigonometry.Line.Parallel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Incidence of points and lines

The line through two distinct points (`line_between`) and its uniqueness up to
proportionality (`line_between_uniq`), together with incidence facts about lines
through the origin.
-/

variable {K : Type*} [Field K]

def line_between : (a b : Point K) → Apart a b → Line K := fun a b anb => ⟨
  b.y - a.y,
  a.x - b.x,
  a.y * b.x - a.x * b.y,
  by
    rcases anb with hx | hy
    · exact Or.inr (sub_ne_zero.mpr hx)
    · exact Or.inl (sub_ne_zero.mpr hy.symm)
⟩

theorem line_between_uniq {a b : Point K} (anb : Apart a b)
: (HasPoint l a ∧ HasPoint l b) ↔ Proportional l (line_between a b anb) := by
  unfold Proportional
  constructor
  · intro ⟨ha, hb⟩
    have hpar : Parallel l (line_between a b anb) := by
      simp only [HasPoint] at ha hb
      simp only [Parallel, line_between]
      linear_combination ha - hb
    obtain ⟨k, hk, hla, hlb⟩ := (para_multiple l (line_between a b anb)).mp hpar
    refine ⟨k, hk, hla, hlb, ?_⟩
    simp only [HasPoint] at ha
    simp only [line_between] at hla hlb ⊢
    linear_combination ha - a.x * hla - a.y * hlb
  · rintro ⟨k, hk, hla, hlb, hlc⟩
    simp only [HasPoint, line_between] at hla hlb hlc ⊢
    exact ⟨by rw [hla, hlb, hlc]; ring, by rw [hla, hlb, hlc]; ring⟩

theorem line0_origin (l : Line0 K) : HasPoint (line0 l) origin
:= by
  unfold HasPoint line0 origin
  simp

theorem line0_negb_a (l : Line0 K) : HasPoint (line0 l) ⟨-l.b, l.a⟩
:= by
  unfold HasPoint line0
  simp
  ring

theorem line0_point (l : Line0 K) : HasPoint (line0 l) p ↔ ∃ c, p = ⟨c * -l.b, c * l.a⟩
:= by
  unfold HasPoint line0
  simp only
  constructor
  · intro lp
    rcases l.ab_ne_zero with an0 | bn0
    · exact ⟨p.y/l.a, Point.ext (by field_simp; linear_combination lp) (by field_simp)⟩
    · exact ⟨-p.x/l.b, Point.ext (by field_simp) (by field_simp; linear_combination lp)⟩
  · rintro ⟨c, rfl⟩
    ring

theorem line_between_a (a b : Point K)
: (anb : Apart a b)
→ HasPoint (line_between a b anb) a
:= by
  unfold Apart HasPoint line_between
  intro anb
  ring

theorem line_between_b (a b : Point K)
: (anb : Apart a b)
→ HasPoint (line_between a b anb) b
:= by
  unfold Apart HasPoint line_between
  intro anb
  ring
