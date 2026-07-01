/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Ring

variable {K : Type*} [Field K]

@[ext] structure Point (K : Type*) [Field K] where
  x : K
  y : K

def Apart (a b : Point K) : Prop :=
  a.x ≠ b.x ∨ a.y ≠ b.y

structure Point3 (K : Type*) [Field K] where
  a₁ : Point K
  a₂ : Point K
  a₃ : Point K
  apart₁ : Apart a₁ a₂
  apart₂ : Apart a₁ a₃
  apart₃ : Apart a₂ a₃

def origin : Point K := ⟨0, 0⟩

namespace Point

instance : Zero (Point K) := ⟨origin⟩
instance : Add (Point K) := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩
instance : Neg (Point K) := ⟨fun p => ⟨-p.x, -p.y⟩⟩
instance : SMul K (Point K) := ⟨fun c p => ⟨c * p.x, c * p.y⟩⟩

@[simp] theorem zero_x : (0 : Point K).x = 0 := rfl
@[simp] theorem zero_y : (0 : Point K).y = 0 := rfl
@[simp] theorem add_x (p q : Point K) : (p + q).x = p.x + q.x := rfl
@[simp] theorem add_y (p q : Point K) : (p + q).y = p.y + q.y := rfl
@[simp] theorem neg_x (p : Point K) : (-p).x = -p.x := rfl
@[simp] theorem neg_y (p : Point K) : (-p).y = -p.y := rfl
@[simp] theorem smul_x (c : K) (p : Point K) : (c • p).x = c * p.x := rfl
@[simp] theorem smul_y (c : K) (p : Point K) : (c • p).y = c * p.y := rfl

instance : AddCommGroup (Point K) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp

instance : Module K (Point K) where
  one_smul := by intros; ext <;> simp
  mul_smul := by intros; ext <;> simp <;> ring
  smul_zero := by intros; ext <;> simp
  smul_add := by intros; ext <;> simp <;> ring
  add_smul := by intros; ext <;> simp <;> ring
  zero_smul := by intros; ext <;> simp

end Point
