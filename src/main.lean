import analysis.asymptotics.asymptotics
import order.filter.at_top_bot
import number_theory.prime_counting
import analysis.special_functions.log.base
import unit_fractions.basic_estimates
import topology.basic

noncomputable theory

open_locale nat big_operators classical filter

open asymptotics filter real nat.arithmetic_function

local notation `π` := nat.prime_counting

lemma pi_def (x : ℝ) : (π ⌊x⌋₊ : ℝ) = ∑ n in (finset.range (⌊x⌋₊ + 1)).filter nat.prime, 1:= 
begin
  have h₁: prime_summatory (λ _, (1 : ℝ)) 1 x = ∑ n in (finset.range (⌊x⌋₊ + 1)).filter nat.prime, 1:=
    begin 
    rw prime_summatory, 
    rw finset.range_eq_Ico,
    rw nat.Ico_succ_right,
    congr' 1,
    simp [finset.ext_iff, nat.one_le_iff_ne_zero, nat.prime.ne_zero] {contextual := tt},
    end,
  rw prime_counting_eq_prime_summatory',
  exact h₁,
end

def at_top_within (s : set ℝ) : filter ℝ := at_top ⊓ 𝓟 s

local notation `⊤[>` x `] `:100 := at_top_within (set.Ioi x)

#check ⊤[>1]

theorem prime_number_theorem : is_O_with 1 ⊤[>1] (λ x, (π ⌊x⌋₊ : ℝ)) (λ x : ℝ, x / log x) := sorry

/-! from unit_fractions.basic_estimation-/
notation `ϑ` := chebyshev_first

lemma lift_ite {a : ℕ} : (ite (nat.prime a) 1 0 : ℝ) = (λ x : ℕ, (ite (nat.prime x) 1 0 : ℝ)) a := rfl

lemma theta_lower_bound (ε x : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2)(hx : 1 < x) : (1 - ε) * ((π ⌊x⌋₊ : ℝ) - (π ⌊x ^ (1 - ε)⌋₊ : ℝ)) * log x ≤ ϑ x := 
begin
  unfold chebyshev_first,
  -- have hle : ⌊x⌋₊ + 1 ≤ ⌊x ^ (1 - ε)⌋₊ + 1 := sorry,
  repeat {rw pi_def},
  rw [mul_comm], 
  rw ←mul_assoc,
  rw ←le_div_iff',
  have h2 : ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), (1 : ℝ) - ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x ^ (1 - ε)⌋₊ + 1)), (1 : ℝ) ≤ ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), (1 : ℝ) := 
  begin
    apply sub_le_self _,
    {
      have h : (0 : ℝ) = ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x ^ (1 - ε)⌋₊ + 1)), 0 := by simp,
      rw h,
      apply finset.sum_le_sum,
      intros x hx,
      simp,
    },
    exact has_add.to_covariant_class_left ℝ,
    exact has_add.to_covariant_class_right ℝ,
  end,
  have h3 : ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), (1 : ℝ) ≤ ((∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), real.log n) / (log x * (1 - ε))) := 
    begin
      rw finset.sum_div,
      apply finset.sum_le_sum,
      intros n hn,
      simp at hn,
      rw one_le_div _,
      repeat{sorry}
    end,
  exact le_trans h2 h3,
  have h4 : 0 < log x := log_pos hx,
  apply (zero_lt_mul_left h4).mpr,
  rw lt_sub,
  simp,
  calc
  ε ≤ 1 / 2 : hε.2
  ... < 1 : one_half_lt_one,
end

lemma theta_lower_bound_2 (ε x : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2)(hx : 1 < x) : (1 - ε) * ((π ⌊x⌋₊ : ℝ) - (π ⌊x ^ (1 - ε)⌋₊ : ℝ)) * log x ≤ ϑ x := 
begin
    have x0: 0 < x:=
    begin
    have h := zero_lt_one,
    exact lt_trans h hx,
    -- calc
    -- x > 1 : hx
    -- ... > 0 : zero_lt_one
    end,
  unfold chebyshev_first,
  repeat {rw pi_def},
  rw [mul_comm], 
  rw ←mul_assoc,
  rw ←le_div_iff',
  have h₁: 0 < log x * (1 - ε):=
        begin
        have h₁₁: 0 < log x:= log_pos hx,
        have h₁₂: 0 < (1 - ε):= begin 
        simp,
        calc
        ε ≤ 1 / 2 : hε.2
        ... < 1 : one_half_lt_one,
        end,
        exact mul_pos h₁₁ h₁₂,
        end,
  have h2 : (((∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), real.log n) - 
  (∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x ^ (1 - ε)⌋₊ + 1)), real.log n)) / (log x * (1 - ε))) ≤ 
  ((∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), real.log n) / (log x * (1 - ε))) := 
  begin
    rw div_le_div_right,
    apply sub_le_self _,
    {
      have h : (0 : ℝ) = ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x ^ (1 - ε)⌋₊ + 1)), 0 := by simp,
      rw h,
      apply finset.sum_le_sum,
      intros x hx,
      exact log_nat_nonneg x,
    },
    exact has_add.to_covariant_class_left ℝ,
    exact has_add.to_covariant_class_right ℝ,
    exact h₁,
  end,
  have h3 : ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), (1 : ℝ)
  - ∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x ^ (1 - ε)⌋₊ + 1)), (1 : ℝ) ≤ 
  (((∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), real.log n) - 
  (∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x ^ (1 - ε)⌋₊ + 1)), real.log n)) / (log x * (1 - ε))) :=
    begin
      rw sub_div,
      rw finset.sum_div,
      repeat{sorry}
    end,
  exact le_trans h3 h2,
  have h4 : 0 < log x := log_pos hx,
  apply (zero_lt_mul_left h4).mpr,
  rw lt_sub,
  simp,
  calc
  ε ≤ 1 / 2 : hε.2
  ... < 1 : one_half_lt_one,
end

lemma theta_upper_bound (x : ℝ)(hx : 1 < x) : ϑ x ≤ (π ⌊x⌋₊ : ℝ) * log x := 
begin
  unfold chebyshev_first,
  rw [pi_def, finset.sum_mul],
  apply finset.sum_le_sum,
  intros i ih,
  simp at ih,
  simp,
  rw [nat.lt_succ_iff, nat.le_floor_iff] at ih,
  rw real.log_le_log,
  exact ih.1,
  simp,
  calc
  0 < 2 : by simp
  ... ≤ i : (nat.prime_def_lt.mp ih.2).1,
  exact lt_trans one_pos hx,
  apply le_of_lt,
  exact lt_trans one_pos hx,
end

#check chebyshev_first_trivial_bound

#check is_O_div_log_prime_counting

#check chebyshev_first_lower

#check chebyshev_upper_explicit

lemma chebyshev_lower_bound : ∃ (a : ℝ), ∀ᶠ (x : ℝ) in at_top, ∥x / log x∥ ≤ a * ∥(π ⌊x⌋₊ : ℝ)∥ := is_O.bound is_O_div_log_prime_counting

lemma chebyshev_upper_bound : ∃ (b : ℝ), ∀ᶠ (x : ℝ) in at_top, ∥(π ⌊x⌋₊ : ℝ)∥ ≤ b * ∥x / log x∥ := is_O.bound is_O_prime_counting_div_log

#check real.norm_of_nonneg

lemma chebyshev_lower_bound' (ε : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2): ∃ (b : ℝ), ∀ᶠ (x : ℝ) in ⊤[>1], (1 - ε) * (π ⌊x⌋₊ : ℝ) ≤ (π ⌊x⌋₊ : ℝ) - 2 * b * x ^ (1 - ε)/ log x := 
begin
  cases chebyshev_lower_bound with a ha,
  cases chebyshev_upper_bound with b hb,
  existsi b,
  sorry
end

lemma chebyshev_upper_bound' (ε : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2): ∃ (b : ℝ), ∀ᶠ (x : ℝ) in ⊤[>1], (π ⌊x⌋₊ : ℝ) - 2 * b * x ^ (1 - ε)/ log x ≤ (π ⌊x⌋₊ : ℝ) - (π ⌊x ^ (1 - ε)⌋₊ : ℝ) := 
begin
  have chebyshev_upper_bound_1 : ∃ (b : ℝ), ∀ᶠ (x : ℝ) in ⊤[>1], (π ⌊x ^ (1 - ε)⌋₊ : ℝ) ≤ b * x ^ (1 - ε)/ log (x ^ (1 - ε)) := sorry,
  have chebyshev_upper_bound_2 : ∃ (b : ℝ), ∀ᶠ (x : ℝ) in ⊤[>1], (π ⌊x ^ (1 - ε)⌋₊ : ℝ) ≤ 2 * b * x ^ (1 - ε)/ log x := sorry,
  sorry,
end

lemma pi_lower_bound (ε : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2) : ∀ᶠ (x : ℝ) in ⊤[>1], (1 - ε) * (π ⌊x⌋₊ : ℝ) ≤ (π ⌊x⌋₊ : ℝ) - (π ⌊x ^ (1 - ε)⌋₊ : ℝ) := sorry

lemma theta_lower_bound' (ε : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2): ∀ᶠ (x : ℝ) in ⊤[>1], (1 - ε) * (π ⌊x⌋₊ : ℝ) * log x ≤ ϑ x := sorry

lemma theta_upper_bound' : ∀ᶠ (x : ℝ) in ⊤[>1], ϑ x ≤ (π ⌊x⌋₊ : ℝ) * log x := sorry

theorem pi_theta : is_O_with 1 ⊤[>1] ϑ id → is_O_with 1 at_top (λ x, (π ⌊x⌋₊ : ℝ)) (λ x : ℝ, x / log x) := sorry
