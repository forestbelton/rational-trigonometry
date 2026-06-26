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
:= by sorry

theorem perp_not_para (l m : Line K)
: Perpendicular l m
→ ¬Parallel l m
:= by sorry

theorem perp_perp_para (l m n : Line K)
: Perpendicular l m
→ Perpendicular l n
→ Parallel m n
:= sorry

theorem perp_of_perp_para (l m n : Line K)
: Perpendicular l m
→ Perpendicular m n
→ Parallel l n
:= sorry

def perp (l : Line K) (p : Point K) : Line K := sorry

theorem perp_perp (l : Line K) (p : Point K) : Perpendicular l (perp l p)
:= sorry

theorem perp_point (l : Line K) (p : Point K) : HasPoint (perp l p) p
:= sorry

theorem perp_unique {l m : Line K}
: Perpendicular l m
→ HasPoint m p
→ Proportional (perp l p) m
:= sorry
