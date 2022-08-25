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

lemma range_sub_eq_Ioc {f : ℕ → ℝ}(a b : ℕ) (h: a ≤ b) : (∑ (n : ℕ) in finset.filter nat.prime (finset.range (b+1)), f n) 
- (∑ (n : ℕ) in finset.filter nat.prime (finset.range (a+1)), f n)
= (∑ (n : ℕ) in finset.filter nat.prime (finset.Ioc a b), f n):=
  begin
    rw finset.range_eq_Ico,
    have h₁: finset.Ico 0 (b + 1) \ finset.Ico 0 (a + 1) = finset.Ioc a b:=
      begin
      rw finset.Ico_diff_Ico_left,
      simp,
      rw ←nat.Ico_succ_succ,
      end,
    rw ← h₁,
    rw sub_eq_iff_eq_add,
    symmetry,
    have h₂: finset.filter nat.prime (finset.Ico 0 (a + 1)) ⊆ finset.filter nat.prime (finset.Ico 0 (b + 1)):=
      begin
      have h₂₁: finset.Ico 0 (a + 1)⊆ finset.Ico 0 (b + 1):=begin
      sorry,
      end,
    rw ←finset.sum_sdiff h₂,
    simp,
    have h₃: finset.filter nat.prime (finset.range (b + 1) \ finset.range (a + 1))= finset.filter nat.prime (finset.range (b + 1)) \ finset.filter nat.prime (finset.range (a + 1)):=sorry,
    rw h₃,
  end

lemma theta_lower_bound_2 (ε x : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2)(hx : 1 < x) : (1 - ε) * ((π ⌊x⌋₊ : ℝ) - (π ⌊x ^ (1 - ε)⌋₊ : ℝ)) * log x ≤ ϑ x := 
begin
  unfold chebyshev_first,
  repeat {rw pi_def},
  rw [mul_comm], 
  rw ←mul_assoc,
  rw ←le_div_iff',
  have x_0 : 0 < x := 
    begin
      calc
      x > 1 : hx
      ... > 0 : zero_lt_one
    end,
  have h1ε: 0 < (1 - ε):= 
    begin 
      simp,
      calc
        ε ≤ 1 / 2 : hε.2
        ... < 1 : one_half_lt_one,
    end,
  have hε1: 1 - ε < 1 :=
    begin
    simp,
    exact hε.1,
  end,
  have ε_0 : 0 < x ^ (1 - ε) := 
    begin
      exact rpow_pos_of_pos x_0 (1 - ε),
    end,
  have log_rpow: log (x ^ (1 - ε)) = log x * (1 - ε):=
    begin
      rw real.log_rpow x_0 (1 - ε),
      rw mul_comm,
    end,
  have pow1_ε: ⌊x ^ (1 - ε)⌋₊ ≤ ⌊x⌋₊:= begin
    have hx_ε : (x ^ (1 - ε)) < (x^(1:ℝ)) := begin
      rw real.rpow_lt_rpow_left_iff,
      exact hε1,
      exact hx,
    end,
    simp at hx_ε,
    have pow1_ε_lt: ⌊x ^ (1 - ε)⌋₊ < ⌊x⌋₊ :=
      begin
    -- theorem nat.floor_lt_ceil_of_lt_of_pos  {a b : α} (h : a < b) (h' : 0 < b) :
    -- ⌊a⌋₊ < ⌈b⌉₊
    -- fail to unify
      sorry,
      end,
    apply le_of_lt,
    exact pow1_ε_lt,
    end,
  have h₁: 0 < log x * (1 - ε):=
    begin
    have h₁₁: 0 < log x:= log_pos hx,
    exact mul_pos h₁₁ h1ε,
    end,
  have hlog : 0 < log (x ^ (1 - ε)) :=
    begin
      rw log_rpow,
      exact h₁,
    end,
  have h₂ : (((∑ (n : ℕ) in finset.filter nat.prime (finset.range (⌊x⌋₊ + 1)), real.log n) - 
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
  have h₃ : ∑ (n : ℕ) in finset.filter nat.prime ((finset.Ioc (⌊x ^ (1 - ε)⌋₊) (⌊x⌋₊))), (1 : ℝ) ≤ 
  ((∑ (n : ℕ) in finset.filter nat.prime (finset.Ioc (⌊x ^ (1 - ε)⌋₊) (⌊x⌋₊)), real.log n) / (log x * (1 - ε))) :=
    begin
      rw ←log_rpow,
      rw finset.sum_div,
      apply finset.sum_le_sum,
      intros i hi,
      rw one_le_div,
      have h₃₁₀: i ∈ finset.Ioc (⌊x ^ (1 - ε)⌋₊) (⌊x⌋₊) := 
        begin 
          apply finset.mem_of_mem_filter i hi,
        end,
      have h₃₁₁ : x ^ (1 - ε) ≤ i := 
        begin
          rw ←nat.Icc_succ_left at h₃₁₀,
          rw nat.succ_eq_add_one at h₃₁₀,
          rw ←nat.floor_add_one at h₃₁₀,
          rw finset.mem_Icc at h₃₁₀,
          have floor_bound : ⌊x ^ (1 - ε) + 1⌋₊ ≤ i := and.elim_left h₃₁₀,
          have floor_le : x ^ (1 - ε) ≤ ⌊x ^ (1 - ε) + 1⌋₊ := 
            begin
              have add_sub : x ^ (1 - ε) = (x ^ (1 - ε) + 1) - 1, {simp},
              have floor_lt : x ^ (1 - ε) < ⌊x ^ (1 - ε) + 1⌋₊ := 
                begin
                  conv
                  begin
                    to_lhs,
                    rw add_sub,
                  end,
                  exact nat.sub_one_lt_floor (x ^ (1 - ε) + 1),
                end,
              exact le_of_lt floor_lt,
            end,
          have coe_le_coe_floor : ⌊x ^ (1 - ε) + 1⌋₊ ≤ i → (⌊x ^ (1 - ε) + 1⌋₊ : ℝ) ≤ (i : ℝ) := 
            begin
              simp,
            end,
          have coe_floor_bound : (⌊x ^ (1 - ε) + 1⌋₊ : ℝ) ≤ (i : ℝ) := 
            begin
              apply coe_le_coe_floor,
              exact floor_bound,
            end,
          exact le_trans floor_le coe_floor_bound,
          have hand : (0 < x ^ (1 - ε)) ∨ (0 = x ^ (1 - ε)) := or.intro_left (0 = x ^ (1 - ε)) ε_0,
          exact le_of_lt_or_eq hand,
        end,
      have h₃₁₂: log (x ^ (1 - ε)) ≤ real.log ↑i :=
        begin
          rw real.log_le_log,
          exact h₃₁₁,
          exact ε_0,
          exact lt_of_lt_of_le ε_0 h₃₁₁,
        end,
      exact h₃₁₂,
      exact hlog,
    end,
  rw ←range_sub_eq_Ioc at h₃,
  rw ←range_sub_eq_Ioc at h₃,
  exact le_trans h₃ h₂,
  exact hpow,
  exact hpow,
  have h₄ : 0 < log x := log_pos hx,
  exact le_trans h₃ h₂,
  have h₆ : 0 < log x := log_pos hx,
  apply (zero_lt_mul_left h₆).mpr,
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
