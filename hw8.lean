import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use


notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r


-- 4a
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . extra
  . obtain ⟨x, hk⟩:= IH
    obtain⟨y, hk_1⟩ := h
    use (a*x + b^k*y)
    calc
      a^(k+1) - b^(k+1) = a*(a^k - b^k) + b^k*(a-b) := by ring
      _ = a * (d * x) + b^k * (d * y) := by rw[hk,hk_1]
      _ = d*(a*x + b^k * y) := by ring


-- 4b
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
    2^(k+1)
      = 2*2^k := by ring
    _ ≥ 2*k^2 := by rel [IH]
    _ = k^2 + k*k := by ring
    _ ≥ k^2 + 4*k := by rel [hk]
    _ = k^2 + 2*k + 2*k := by ring
    _ ≥ k^2 + 2*k + 2*4 := by rel [hk]
    _ = k^2 + 2*k + 1 + 7 := by ring
    _ = (k+1)^2 + 7 := by ring
    _ ≥ (k+1)^2 := by extra

--4c
theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  . simp
  . have ha : 0 ≤ 1+a := by addarith [ha]
    have h1 : (1 + a)^(k+1) ≥ 1 + (k+1)*a := by
      calc
        (1+a)^(k+1)
        = (1+a) * (1+a)^k := by ring
        _ ≥ (1 + a) * (1 + k*a) := by rel[IH]
        _ = 1 + a + k*a + k*a^2 := by ring
        _ = 1 + a*(1+k) + k*a^2 := by ring
        _ ≥ 1 + a*(1+k) := by extra
    apply h1


--4d
example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  . -- base case
    numbers
  . -- inductive step
    calc
      (3:ℤ)^(k+1) = 3^k * 2 + 3^k  := by ring
      _ ≥ 3^k*2 := by extra
      _ ≥ (2^k + 100)*2 := by rel[IH]
      _ = 2^(k+1) + 2*100 := by ring
      _ = 2^(k+1) + 100 + 100 := by ring
      _ ≥ 2^(k+1) + 100 := by extra


def foo : ℕ → ℕ
  | 0     => 0
  | n + 1 => foo (n) + 2 * n + 1


--5b
theorem problem5b {n : ℕ} : ∃ (k : ℕ), foo (n) = k ^ 2 := by
  use n
  simple_induction n with k hk
  . simp
  . simp [foo]
    have hk_1 : foo (k)+ 2*k + 1 = (k+1)^2 := by
      calc
        foo (k) + 2 * k + 1 = k^2 + 2*k + 1 := by rw[hk]
        _ = (k + 1)^2 := by ring
    apply hk_1
