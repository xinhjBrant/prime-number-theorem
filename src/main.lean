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

def at_top_within (s : set ℝ) : filter ℝ := at_top ⊓ 𝓟 s

local notation `⊤[>` x `] `:100 := at_top_within (set.Ioi x)

#check ⊤[>1]

theorem prime_number_theorem : is_O_with 1 ⊤[>1] (λ x, (π ⌊x⌋₊ : ℝ)) (λ x : ℝ, x / log x) := sorry

/-! from unit_fractions.basic_estimation-/
notation `ϑ` := chebyshev_first

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

lemma theta_lower_bound (ε : ℝ)(hε : 0 < ε ∧ ε ≤ 1 /2): ∀ᶠ (x : ℝ) in ⊤[>1], (1 - ε) * (π ⌊x⌋₊ : ℝ) * log x ≤ ϑ x := sorry

lemma theta_upper_bound : ∀ᶠ (x : ℝ) in ⊤[>1], ϑ x ≤ (π ⌊x⌋₊ : ℝ) * log x := sorry

theorem pi_theta : is_O_with 1 ⊤[>1] ϑ id → is_O_with 1 at_top (λ x, (π ⌊x⌋₊ : ℝ)) (λ x : ℝ, x / log x) := sorry
