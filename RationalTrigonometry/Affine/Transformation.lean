/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import RationalTrigonometry.Line.Defs

import PolyrithLocal.Polyrith

variable {K : Type u} [Field K]

def AffineTransformation (t : Point K → Point K) : Prop
:= (p q : Point K)
→ (c₁ c₂ : K)
→ c₁ + c₂ = 1
→ t (c₁ • p + c₂ • q) = c₁ • (t p) + c₂ • (t q)

def rotate (a : Point K) : Point K → Point K
:= fun b => (2 : K) • a + (-1 : K) • b

theorem rotate_affine : (a : Point K) → AffineTransformation (rotate a)
:= by
  unfold AffineTransformation rotate
  intro a p q c₁ c₂ cs1
  ext <;> simp
  · linear_combination -(2 * a.x * cs1)
  · linear_combination -(2 * a.y * cs1)
