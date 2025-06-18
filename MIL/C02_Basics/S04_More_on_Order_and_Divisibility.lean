import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

#check (le_of_max_le_left : max a b ≤ c → a ≤ c)
#check (max_le_max : a ≤ b → c ≤ d → max a c ≤ max b d)
#check (le_max_left a b : a ≤ max a b)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    · show a ≤ max b a
      apply le_max_right
    · show b ≤ max b a
      apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    · show b ≤ max a b
      apply le_max_right
    · show a ≤ max a b
      apply le_max_left

theorem double_min_le_the_first : min (min a b) c ≤ a := by
  have h₁ : min a b ≤ a := min_le_left a b
  have h₂ : min (min a b) c ≤ min a b := min_le_left (min a b) c
  apply le_trans h₂ h₁

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · show min (min a b) c ≤ a
      apply double_min_le_the_first
    · show min (min a b) c ≤ min b c
      apply le_min
      · show min (min a b) c ≤ b
        rw[min_comm a b]
        apply double_min_le_the_first
      · show min (min a b) c ≤ c
        apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · show min a (min b c) ≤ min a b
      apply le_min
      · show min a (min b c) ≤ a
        apply min_le_left
      · show min a (min b c) ≤ b
        rw [min_comm]
        apply double_min_le_the_first
    · show min a (min b c) ≤ c
      rw[min_comm, min_comm b c]
      apply double_min_le_the_first

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show min a b + c ≤ a + c
    have h₁ : min a b ≤ a := min_le_left a b
    apply add_le_add_right h₁ c
  · show min a b + c ≤ b + c
    have h₂ : min a b ≤ b := min_le_right a b
    apply add_le_add_right h₂ c



example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · show min a b + c ≤ min (a + c) (b + c)
    apply aux
  · show min (a + c) (b + c) ≤ min a b + c
    have h₁ : min (a+c) (b+c) - c ≤ min a b := by
      apply le_min
      · show min (a+c) (b+c) - c ≤ a
        have h₃ : min (a+c) (b+c) ≤ a + c := min_le_left (a+c) (b+c)
        linarith
      · show min (a+c) (b+c) - c ≤ b
        have h₄ : min (a+c) (b+c) ≤ b + c := min_le_right (a+c) (b+c)
        linarith
    linarith


#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h : |a| ≤ |a - b| + |b| := by
    have h' : |a - b + b| ≤ |a - b| + |b| := abs_add (a-b) b
    have h'' : a - b + b = a := by linarith
    rw [h''] at h'
    exact h'
  linarith

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

#check (dvd_mul_right)

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h₁ : x ∣ y * (x * z) := by
    have h' : y * (x * z) = x * (y * z) := by linarith
    rw [h']
    apply dvd_mul_right
  have h₂ : x ∣ x ^ 2 := dvd_mul_left _ _
  have h₃ : x ∣ w ^ 2 := by
    have h'' : w ∣ w ^ 2 := dvd_mul_left _ _
    apply dvd_trans h h''
  have h₄ : x ∣ y * (x * z) + x ^ 2 := dvd_add h₁ h₂
  apply dvd_add h₄ h₃
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  · show Nat.gcd m n ∣ Nat.gcd n m
    apply dvd_gcd
    · show Nat.gcd m n ∣ n
      apply Nat.gcd_dvd_right
    · show Nat.gcd m n ∣ m
      apply Nat.gcd_dvd_left
  · show Nat.gcd n m ∣ Nat.gcd m n
    apply dvd_gcd
    · show Nat.gcd n m ∣ m
      apply Nat.gcd_dvd_right
    · show Nat.gcd n m ∣ n
      apply Nat.gcd_dvd_left
end
