import analysis.p_series
import number_theory.arithmetic_function
import analysis.special_functions.log.basic
import data.finset.basic
import topology.algebra.infinite_sum
import topology.bases
import topology.uniform_space.basic
import tactic.abel
import tactic.linarith
import analysis.normed_space.basic
import topology.algebra.order.liminf_limsup
import topology.local_homeomorph

noncomputable theory

universes u v

open filter topological_space set classical uniform_space function
open_locale classical uniformity topological_space filter

variables {α : Type u} {β : Type v} [uniform_space α]
open finset
open_locale big_operators
open filter set
open_locale topological_space big_operators classical filter nnreal

namespace asymptotics

namespace nat
namespace arithmetic_function
variable (R : Type*)
section has_zero
variable [has_zero R]

localized "notation `ζ` := nat.arithmetic_function.zeta" in arithmetic_function
notation `⌊` a `⌋₊` := nat.floor a

--Already Have...
--counts the number of prime numbers less than x.
def pi : ℕ → ℕ := λ(x: ℕ), ((range x).filter prime).card
def pi_eps (eps: ℝ) : ℕ → ℕ := λ(x: ℕ), ((Ioc (x:ℝ)^((1:ℝ) - eps) (x:ℝ)).filter prime).card
def zeta': ℂ → ℂ:= λ (x:ℂ ), ∑'n, 1 / (n ^ x)
def p_log : ℕ → ℝ  := λ (x:ℕ ), if hx : prime x  then real.log x else 0
def theta :ℕ → ℝ := λ (x : ℕ), ∑ p in range x, p_log p
def phi  : ℂ → ℂ := λ (s : ℂ), ∑'p, (p_log p) / (p ^ s)


def PNTfunc: ℕ → ℝ :=  λ(x: ℕ), (pi x:ℝ ) / ((x:ℝ ) /real.log (x:ℝ):ℝ)
def thetafunc:ℕ → ℝ :=  λ(x: ℕ), theta x/ (x:ℝ)

theorem tendsto_equiv_has_bound (seq : ℕ → ℝ): 
tendsto seq at_top (𝓝 1) ↔ ∀ c_1 < 1, ∀ c_2 > 1, 
∃ N, ∀ n ≥ N, c_1 < seq n ∧ seq n < c_2 :=
begin
  rw [at_top_basis.tendsto_iff (nhds_basis_Ioo (1 : ℝ))],
  simp only [set.mem_Ici, set.mem_Ioo, exists_true_left, 
  and_imp, prod.forall, gt_iff_lt,
    ge_iff_le],
  exact forall_congr (λ _, forall_swap),
  apply_instance,
end

theorem PNT : tendsto PNTfunc at_top (𝓝 1)
:=begin
rw tendsto_equiv_has_bound,
have statement_1: tendsto thetafunc at_top (𝓝 1):=begin 
   rw tendsto_equiv_has_bound, 
   sorry,end,
have h₁: ∀ ε ∈ Ioc 0 (1/2), ∀ x > 1, theta x ≤ (real.log x)* pi x:=sorry,
sorry,
end

lemma have_bounds_equiv_is_O:
∃ a > 0, ∃b > a, 
∃ N :ℕ, ∀ n ≥ N, a < PNTfunc n ∧ PNTfunc n < b ↔ is_O at_top (λ x, (pi x : ℝ)) (λ x, x / real.log x):=sorry



theorem Chebyshevs_bounds: ∃ a > 0, ∃b > a, 
∃ N :ℕ, ∀ n ≥ N, a < PNTfunc n ∧ PNTfunc n < b:=
begin
/-have h₁: ∃ N :ℕ, ∀ n ≥ N, (4/3)^n ≤ ((range 2* n).filter prime):=sorry,-/
sorry,
end

--my attempt
lemma step₁ (n: ℕ): choose (2*n) n < (4^n):=
begin
have h₁: (4^n) = ((1+1)^(2*n)):=begin
 have h₁₁: (4^n) = (2^2)^n:=by ring,
 rw h₁₁,
 rw pow_mul,
 end,
rw h₁,
have h₂: ((1+1)^(2*n)) = ∑ k in range (2*n), choose (2*n) k:=begin
sorry,
end,
rw h₂,
sorry,
end

lemma step₂ (n: ℕ): choose (2*n) n ≥  (2^n):=
begin
induction n with d hd,
simp,
sorry,
end



end nat
end arithmetic_function

end