import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- problem 4a
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7*k + 1
  calc
    7*n - 4 = 7*(2*k + 1) - 4 := by rw [hk]
    _ = 2*(7*k + 1) + 1 := by ring

-- 4b 
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨k, hox⟩ := hx
  obtain ⟨q, hoy⟩ := hy
  use 2*k*q + 3*q + k + 1
  calc
    x*y + 2*y = (2*k + 1)*y + 2*y := by rw [hox]
    _ = (2*k  + 1)*(2*q + 1) + 2*(2*q + 1) :=  by rw [hoy]
    _ = 2*(2*k*q + 3*q + k + 1) + 1 := by ring

-- 4c
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Odd] at *
  obtain ⟨k, hek⟩ := hn
  use 2*k*k + 2*k - 3
  calc
    n^2 + 2*n - 5 = (k+k)^2 + 2*(k+k) - 3 := by rw [hek]
    _ = 2*(2*k*k + 2*k - 3) + 1 := by ring  

--4d
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain hbc | hbc := Int.even_or_odd (b - c)
  . right
    right
    obtain ⟨x, hbc⟩ := hbc
    use x
    calc
      b - c = 2 * x := by rw[hbc]
      _ = x + x := by ring 
  . obtain hac | hac := Int.even_or_odd (a + c)
    . right
      left
      obtain ⟨x, hac⟩ := hac
      use x
      calc
        a + c = 2 * x := by rw[hac]
        _ = x + x := by ring
    . left
      obtain ⟨x, hac⟩ := hac
      obtain ⟨y, hbc⟩ := hbc
      use (x - y - c)
      calc
        a - b = (a+c) - (b-c) - 2 * c := by ring
        _ = (2 * x + 1) - (b - c) - 2 * c := by rw[hac]
        _ = (2 * x + 1) - (2 * y + 1) - 2 * c := by rw[hbc]
        _ = 2 * x - 2 * y - 2 * c := by ring
        _ = 2 * (x - y - c) := by ring
        _ = (x-y-c) + (x-y-c) := by ring
        _ = 2*(x-y-c)

--5a
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have hab : (a+b)/2 ≥ a ∨ (a+b)/2 ≤ b := by apply h
  obtain ha | hb := hab
  . calc
      b = 2 * ((a + b) / 2) - a := by ring
      _ ≥ 2 * a - a := by rel [ha]
      _ = a := by ring
  . calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [hb]
      _ = b := by ring  


-- 5b
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h
  have hp : -3 ≤ (x+y) ∧ (x+y) ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc 
      (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by extra
      _ = 2 * (x^2 + y^2) := by ring
      _ ≤ 2 * 4 := by rel[h]
      _ ≤  3 ^ 2 := by numbers
    numbers
  addarith[hp]

-- 5c
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h3 := hn 3
  simp at h3 
  have h5 := hn 5
  simp at h5
  obtain ⟨a, ha⟩ := h3
  obtain ⟨b, hb⟩ := h5
  use -3 * b + 2 * a
  calc 
    n = -9 * n  + 10 * n := by ring
    _ = -9 * (5 * b) + 10 * n := by rw[hb]
    _ = 15 * (-3 * b) + 10 * n := by ring
    _ = 15 * (-3 * b) + 10 * (3 * a) := by rw[ha]
    _ = 15 * (-3 * b) + 15 * (2 * a) := by ring
    _ = 15 * (-3 * b + 2 * a) := by ring


-- 5d
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 10
  intro x hx
  calc
    x^3 + 3*x = x * x^2 + 3*x := by ring
    _ ≥ 10 * x^2 + 3*10 := by rel[hx]
    _ = 7 * x^2 + 12 + (3*x^2 + 18):= by ring
    _ ≥ 7 * x^2 + 12 := by extra


-- 6 a
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have h1: (x + 3) * (x - 2) = 0 := by
      calc
        (x + 3) * (x - 2) = x^2 + x - 6 := by ring
        _ = 0 := by rw[h]
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain hx3 | hx2 := h2
    left
    . calc
        x = (x + 3) - 3 := by ring
        _ = 0 - 3 := by rw[hx3]
        _ = -3 := by numbers
    right
    . calc
        x = (x - 2) + 2 := by ring
        _ = 0 + 2 := by rw[hx2]
        _ = 2 := by numbers
  . intro h
    obtain hx3 | hx2 := h
    . calc
        x^2 + x - 6 = (x + 3) * (x - 2) := by ring
        _ = (-3 + 3) * (x - 2) := by rw[hx3]
        _ = 0 := by ring
    . calc 
        x^2 + x - 6 = (x - 2) * (x + 3) := by ring
        _ = (2 - 2) * (x + 3) := by rw[hx2]
        _ = 0 := by ring

-- 6 b
example {a : ℤ} : a^2 - 5*a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h
    have h1 := calc 
      (2*a-5)^2 = 4*(a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * -1 + 5 := by rel[h]
      _ = 1^2 := by ring
    have h2 : (0:ℤ) ≤1 := by numbers
    obtain ⟨h3, h4⟩ := abs_le_of_sq_le_sq' h1 h2
    have h3 : 2*2 ≤ 2*a := by addarith[h3]
    cancel 2 at h3
    have h4 : 2*a ≤ 2*3 := by addarith[h4]
    cancel 2 at h4
    interval_cases a
    · left; numbers
    · right; numbers
  . intro h
    obtain ha2 | ha3 := h
    . rw [ha2]
      numbers
    . rw [ha3]
      numbers
