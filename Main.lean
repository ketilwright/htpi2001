
import HTPILib.IntroLean
import HTPILib.Chap7
--import Library.Basic --collision with ⊈ notation between HTPIwL & Math2001
import Library.Tactic.Numbers.Basic
import Library.Tactic.Cancel
import Library.Tactic.Exhaust
import Library.Tactic.Extra.Basic
import Library.Tactic.Induction
-- TODO: some sort of "master" import might be useful
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

-- From HTPIwL
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  assume h3: P
  show R from h2 (h1 h3)




/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := by
       --  From the definition of ℕ division we know:
    have h3: b * (a / b) + a % b = a := Nat.div_add_mod a b
    --  Since d divides b, d divides any product of b
    have h4: d ∣ b * (a / b) := Dvd.dvd.mul_right h1 (a / b)
    --  Since d ∣ a % b, and d ∣ b * (a / b), d ∣ b * (a / b) + a % b
    rewrite [←h3]
    show _ from Nat.dvd_add h4 h2

--from math2001

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  ·
    intro hk
    -- we have k² ≤ 6 < 3²
    have h1:=
      calc k ^ 2
        _ ≤ 6 := hk
        _ < 3 ^ 2 := by numbers
    -- Since k² < 9, k < 3
    cancel 2 at h1 -- section 2.1.5: cancel works on exponents.
    -- Since k ∈ ℕ < 3, we are done
    interval_cases (k)
    left; numbers
    right; left; numbers
    right; right; numbers
  ·
    intro hk
    obtain h1 | h1 := hk
    calc k ^ 2
      _ = 0 ^ 2 := by rw [h1]
      _ ≤ 6 := by numbers
    obtain h2 | h2 := h1
    calc k ^ 2
      _ = 1 ^ 2 := by rw [h2]
      _ ≤ 6 := by numbers
    calc k ^ 2
      _ = 2 ^ 2 := by rw [h2]
      _ ≤ 6 := by numbers

--htpi style:
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  apply Iff.intro
  ·
    assume h1: k ^ 2 ≤ 6 -- intro does not allow printing
                         -- the antecedent
    have h2:=
      calc k ^ 2
        _ ≤ 6 := h1
        _ < 3 ^ 2 := by linarith /- notin MOP, but HTPI makes avail-/
    cancel 2 at h2 -- or lt_of_pow_lt_pow in htpi
    -- suppose k ∉ {0, 1, 2}
    by_contra h3
    push_neg at h3 -- works better than demorgan when there's more than one disjunction
    obtain ⟨h4, h5, h6⟩ := h3
    have h8: k ≠ 0 → k ≥ 1 := by intro _; apply Nat.one_le_iff_ne_zero.mpr h4
    have h9: k > 1 ∨ k = 1 := LE.le.gt_or_eq (h8 h4)
    disj_syll h9 h5
    have h10: k = 2 :=  Nat.eq_of_le_of_lt_succ h9 h2
    contradiction

    -- interval_cases is slick but opaque
    -- interval_cases k
    -- or_left; rfl
    -- or_right; or_left; rfl
    -- right; right; ring
  ·
    assume h3: k = 0 ∨ k = 1 ∨ k = 2
    obtain (k0: k = 0) | (k1: k = 1) | (k2: k = 2) := h3
    ·
      show k ^ 2 ≤ 6 from
        calc k ^ 2
          _ = 0 ^ 2 := by rw [k0]
          _ ≤ 6 := by numbers
    · -- or just:
      rw [k1]; numbers
    ·
      rewrite [k2]; numbers
