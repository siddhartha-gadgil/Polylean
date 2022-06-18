import Mathlib.Algebra.Group.Defs

/-
Source: https://en.wikipedia.org/wiki/Word_problem_(mathematics)#Example:_A_term_rewriting_system_to_decide_the_word_problem_in_the_free_group
-/

namespace Group

variable {G : Type _} [Group G] (x y z : G)

-- the group axioms

attribute [simp] one_mul

attribute [simp] mul_left_inv

attribute [simp] mul_assoc

attribute [simp] mul_one

@[simp] theorem left_inv_cancel : x⁻¹ * (x * y) = y := by rw [← mul_assoc]; simp

@[simp] theorem one_inv : (1 : G)⁻¹ = (1 : G) := by
  have := left_inv_cancel (1 : G) (1 : G)
  rw [mul_one, mul_one] at this; assumption

@[simp] theorem inv_inv : (x⁻¹)⁻¹ = x := by
  have := left_inv_cancel (x⁻¹) x
  rw [mul_left_inv, mul_one] at this; assumption

@[simp] theorem mul_right_inv : x * x⁻¹ = 1 := by
  have := left_inv_cancel (x⁻¹) (1 : G)
  rw [inv_inv, mul_one] at this; assumption

@[simp] theorem left_cancel_inv : x * (x⁻¹ * y) = y := by
  have := left_inv_cancel (x⁻¹) y
  rw [inv_inv] at this; assumption

@[simp] theorem prod_inv : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  have := left_cancel_inv (x * y)⁻¹ (y⁻¹ * x⁻¹)
  simp at this; assumption

end Group


variable {G : Type _} [Group G] (a b c : G)

example : ((a⁻¹ * a) * (b * b⁻¹))⁻¹ = (1 : G) := by simp

example : b * ((a * b)⁻¹ * a) = 1 := by simp

example : a * (c⁻¹ * b) * (((b⁻¹ * c) * b) * (a * b)⁻¹) = (1 : G) := by simp
